use crate::{
    type_checking::{
        Constraint, StructField, TypeNameOrPlaceholder, TypeUnderConstruction, TypeVar, UnionMember,
    },
    util::LinkedList,
};
use anyhow::{Context, Result, bail};
use std::collections::{HashMap, VecDeque};
use thiserror::Error;

type Substitution = HashMap<TypeVar, TypeUnderConstruction>;

#[derive(Debug, Clone, Error)]
enum UnificationError {
    #[error(
        "Infinite type detected: type variable '{var}' occurs within its own definition\n  This typically occurs when a function is defined recursively without a base case.\n\n  Attempted to unify: {var} = {ty}"
    )]
    UnconstructableInfiniteType {
        var: TypeVar,
        ty: TypeUnderConstruction,
    },

    #[error(
        "Tuple size mismatch: cannot unify tuples of different lengths\n  Expected: {expected} element(s)\n  Found: {found} element(s)"
    )]
    TupleSizeMismatch { expected: usize, found: usize },

    #[error(
        "Struct name mismatch: cannot unify different struct types\n  Type 1: {left}\n  Type 2: {right}"
    )]
    StructNameMismatch {
        left: TypeNameOrPlaceholder,
        right: TypeNameOrPlaceholder,
    },

    #[error(
        "Union name mismatch: cannot unify different union types\n  Type 1: {left}\n  Type 2: {right}"
    )]
    UnionNameMismatch {
        left: TypeNameOrPlaceholder,
        right: TypeNameOrPlaceholder,
    },

    #[error(
        "Type mismatch: failed to unify incompatible types\n  Type 1: {left}\n  Type 2: {right}"
    )]
    IncompatibleTypes {
        left: TypeUnderConstruction,
        right: TypeUnderConstruction,
    },
}

pub fn solve_constraints(constraints: Vec<Constraint>) -> Result<Substitution> {
    let mut subst = Substitution::new();
    let mut remaining: VecDeque<_> = constraints.into();

    while let Some(constraint) = remaining.pop_front() {
        match constraint {
            Constraint::Equal(ref t1, ref t2) => {
                let t1_applied = apply_substitution(t1, &subst);
                let t2_applied = apply_substitution(t2, &subst);

                match (t1_applied.clone(), t2_applied.clone()) {
                    (TypeUnderConstruction::Var(v), ty) | (ty, TypeUnderConstruction::Var(v)) => {
                        if occurs_check(&v, &ty) {
                            bail!(UnificationError::UnconstructableInfiniteType {
                                var: v.clone(),
                                ty: ty.clone(),
                            });
                        }

                        subst.insert(v.clone(), ty.clone());

                        // Apply new substitution to remaining constraints
                        remaining = remaining
                            .into_iter()
                            .map(|c| apply_substitution_to_constraint(&c, &subst))
                            .collect();
                    }
                    (ty1, ty2) => {
                        unify(&ty1, &ty2, &mut remaining)
                            .with_context(|| format!("While solving constraint {} = {}", ty1, ty2))
                            .with_context(|| UnificationError::IncompatibleTypes {
                                left: ty1.clone(),
                                right: ty2.clone(),
                            })?;
                    }
                }
            }
            Constraint::Subtype(t1, t2) => {
                // For now, treat subtype as equality
                remaining.push_back(Constraint::Equal(t1.clone(), t2.clone()));
            }
        }
    }

    Ok(subst)
}

fn unify(
    ty1: &TypeUnderConstruction,
    ty2: &TypeUnderConstruction,
    constraints: &mut VecDeque<Constraint>,
) -> Result<()> {
    match (ty1, ty2) {
        (TypeUnderConstruction::Var(v1), TypeUnderConstruction::Var(v2)) => {
            constraints.push_back(Constraint::Equal(
                TypeUnderConstruction::Var(v1.clone()),
                TypeUnderConstruction::Var(v2.clone()),
            ));
            Ok(())
        }
        (TypeUnderConstruction::Function(args1), TypeUnderConstruction::Function(args2)) => {
            match (args1.peek(), args2.peek()) {
                ((arg1, Some(args1)), (arg2, Some(args2))) => {
                    constraints.push_back(Constraint::Equal(arg1.clone(), arg2.clone()));
                    constraints.push_back(Constraint::Equal(
                        TypeUnderConstruction::Function(Box::new(args1.clone())),
                        TypeUnderConstruction::Function(Box::new(args2.clone())),
                    ));
                }
                ((arg1, None), (arg2, None)) => {
                    constraints.push_back(Constraint::Equal(arg1.clone(), arg2.clone()));
                }
                ((ty, None), (arg, Some(args))) | ((arg, Some(args)), (ty, None)) => {
                    constraints.push_back(Constraint::Equal(
                        ty.clone(),
                        TypeUnderConstruction::Function(Box::new(LinkedList::new(
                            arg.clone(),
                            args.clone(),
                        ))),
                    ));
                }
            }
            Ok(())
        }
        (TypeUnderConstruction::Tuple(elems1), TypeUnderConstruction::Tuple(elems2)) => {
            if elems1.len() != elems2.len() {
                return Err(UnificationError::TupleSizeMismatch {
                    expected: elems1.len(),
                    found: elems2.len(),
                })
                .with_context(|| format!("Tuple types:\n  Type 1: {}\n  Type 2: {}", ty1, ty2))?;
            }

            for (e1, e2) in elems1.iter().zip(elems2.iter()) {
                constraints.push_back(Constraint::Equal(e1.clone(), e2.clone()));
            }
            Ok(())
        }
        (
            TypeUnderConstruction::Struct(n1, fields1),
            TypeUnderConstruction::Struct(n2, fields2),
        ) => {
            if n1 != n2 {
                return Err(UnificationError::StructNameMismatch {
                    left: n1.clone(),
                    right: n2.clone(),
                })
                .with_context(|| {
                    format!(
                        "Cannot unify structs with different names:\n  Struct 1 has {} field(s)\n  Struct 2 has {} field(s)",
                        fields1.len(),
                        fields2.len()
                    )
                })?;
            }
            Ok(())
        }

        (TypeUnderConstruction::Union(n1, _), TypeUnderConstruction::Union(n2, _)) => {
            if n1 != n2 {
                bail!(UnificationError::UnionNameMismatch {
                    left: n1.clone(),
                    right: n2.clone(),
                });
            }
            Ok(())
        }
        (TypeUnderConstruction::RecurseMarker(s1), TypeUnderConstruction::RecurseMarker(s2)) => {
            if s1 != s2 {
                return Err(UnificationError::UnionNameMismatch {
                    left: s1.clone().into(),
                    right: s2.clone().into(),
                })
                .context("Cannot unify different recursive type markers")?;
            }
            Ok(())
        }
        (
            TypeUnderConstruction::RecurseMarker(s),
            TypeUnderConstruction::Struct(TypeNameOrPlaceholder::Symbol(name), _),
        )
        | (
            TypeUnderConstruction::Struct(TypeNameOrPlaceholder::Symbol(name), _),
            TypeUnderConstruction::RecurseMarker(s),
        ) => {
            if s != name {
                bail!(UnificationError::StructNameMismatch {
                    left: s.clone().into(),
                    right: name.clone().into()
                });
            }
            Ok(())
        }
        (
            TypeUnderConstruction::RecurseMarker(s),
            TypeUnderConstruction::Union(TypeNameOrPlaceholder::Symbol(name), _),
        )
        | (
            TypeUnderConstruction::Union(TypeNameOrPlaceholder::Symbol(name), _),
            TypeUnderConstruction::RecurseMarker(s),
        ) => {
            if s != name {
                return Err(UnificationError::UnionNameMismatch {
                    left: s.clone().into(),
                    right: name.clone().into(),
                })
                .context("Recursive type marker does not match union name")?;
            }
            Ok(())
        }
        (ty1, ty2) => bail!(UnificationError::IncompatibleTypes {
            left: ty1.clone(),
            right: ty2.clone(),
        }),
    }
}

fn occurs_check(var: &TypeVar, ty: &TypeUnderConstruction) -> bool {
    match ty {
        TypeUnderConstruction::Var(v) => v == var,
        TypeUnderConstruction::Function(args) => args.iter().any(|arg| occurs_check(var, arg)),
        TypeUnderConstruction::Tuple(elems) => elems.iter().any(|e| occurs_check(var, e)),
        TypeUnderConstruction::Struct(_, fields) => {
            fields.iter().any(|f| occurs_check(var, &f.field_type))
        }
        TypeUnderConstruction::Union(_, members) => members
            .iter()
            .any(|m| m.member_type().is_some_and(|t| occurs_check(var, t))),
        TypeUnderConstruction::RecurseMarker(_) => false,
    }
}

fn apply_substitution_to_constraint(c: &Constraint, subst: &Substitution) -> Constraint {
    match c {
        Constraint::Equal(t1, t2) => {
            Constraint::Equal(apply_substitution(t1, subst), apply_substitution(t2, subst))
        }
        Constraint::Subtype(t1, t2) => {
            Constraint::Subtype(apply_substitution(t1, subst), apply_substitution(t2, subst))
        }
    }
}

fn apply_substitution(ty: &TypeUnderConstruction, subst: &Substitution) -> TypeUnderConstruction {
    match ty {
        TypeUnderConstruction::Var(v) => {
            if let Some(t) = subst.get(v) {
                // Follow the chain of substitutions
                apply_substitution(t, subst)
            } else {
                ty.clone()
            }
        }
        TypeUnderConstruction::Function(args) => {
            let args = args
                .iter()
                .map(|a| apply_substitution(a, subst))
                .collect::<Vec<_>>();

            let args = args
                .try_into()
                .expect("We had arguments before, I they did not disappear");
            TypeUnderConstruction::Function(Box::new(args))
        }

        TypeUnderConstruction::Tuple(elems) => TypeUnderConstruction::Tuple(
            elems.iter().map(|e| apply_substitution(e, subst)).collect(),
        ),
        TypeUnderConstruction::Struct(name, fields) => TypeUnderConstruction::Struct(
            name.clone(),
            fields
                .iter()
                .map(|f| StructField {
                    name: f.name.clone(),
                    field_type: apply_substitution(&f.field_type, subst),
                })
                .collect(),
        ),
        TypeUnderConstruction::Union(name, members) => TypeUnderConstruction::Union(
            name.clone(),
            members
                .iter()
                .map(|m| match m {
                    UnionMember::SingletonUnionMember(n) => {
                        UnionMember::SingletonUnionMember(n.clone())
                    }
                    UnionMember::UnionMember(n, t) => {
                        UnionMember::UnionMember(n.clone(), apply_substitution(t, subst))
                    }
                })
                .collect(),
        ),
        TypeUnderConstruction::RecurseMarker(_) => ty.clone(),
    }
}
