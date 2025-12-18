use crate::{
    type_checking::{
        Constraint, StructField, SymbolOrPlaceholder, TypeUnderConstruction, TypeVar, UnionMember,
    },
    util::LinkedList,
};
use anyhow::{Context, Result, bail};
use std::collections::{HashMap, VecDeque};
use thiserror::Error;

type Substitution = HashMap<TypeVar, TypeUnderConstruction>;

#[derive(Debug, Clone, Error)]
enum UnificationError {
    #[error("Encountered an unconstructable infinite type: {ty}")]
    UnconstructableInfiniteType { ty: TypeUnderConstruction },

    #[error("Function arity mismatch: expected {expected} arguments, got {found}")]
    FunctionArityMismatch { expected: usize, found: usize },

    #[error("Tuple size mismatch: expected {expected} elements, got {found}")]
    TupleSizeMismatch { expected: usize, found: usize },

    #[error("Struct name mismatch: cannot unify '{left}' with '{right}'")]
    StructNameMismatch {
        left: SymbolOrPlaceholder,
        right: SymbolOrPlaceholder,
    },

    #[error("Union name mismatch: cannot unify '{left}' with '{right}'")]
    UnionNameMismatch {
        left: SymbolOrPlaceholder,
        right: SymbolOrPlaceholder,
    },

    #[error("Cannot unify incompatible types:\n  Type 1: {left}\n  Type 2: {right}")]
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
                            bail!(UnificationError::UnconstructableInfiniteType { ty: ty.clone() });
                        }
                        subst.insert(v.clone(), ty.clone());

                        // Apply new substitution to remaining constraints
                        remaining = remaining
                            .into_iter()
                            .map(|c| apply_substitution_to_constraint(&c, &subst))
                            .collect();
                    }

                    (ty1, ty2) => {
                        unify(&ty1, &ty2, &mut remaining).with_context(|| {
                            UnificationError::IncompatibleTypes {
                                left: ty1.clone(),
                                right: ty2.clone(),
                            }
                        })?;
                    }
                }
            }

            Constraint::Subtype(t1, t2) => {
                // For now, treat subtype as equality
                remaining.push_back(Constraint::Equal(t1, t2));
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

        (
            TypeUnderConstruction::Function(args1, ret1),
            TypeUnderConstruction::Function(args2, ret2),
        ) => {
            if args1.len() != args2.len() {
                bail!(UnificationError::FunctionArityMismatch {
                    expected: args1.len(),
                    found: args2.len()
                });
            }

            for (a1, a2) in args1.iter().zip(args2.iter()) {
                constraints.push_back(Constraint::Equal(a1.clone(), a2.clone()));
            }

            constraints.push_back(Constraint::Equal(
                ret1.as_ref().clone(),
                ret2.as_ref().clone(),
            ));
            Ok(())
        }

        (TypeUnderConstruction::Tuple(elems1), TypeUnderConstruction::Tuple(elems2)) => {
            if elems1.len() != elems2.len() {
                bail!(UnificationError::TupleSizeMismatch {
                    expected: elems1.len(),
                    found: elems2.len()
                });
            }

            for (e1, e2) in elems1.iter().zip(elems2.iter()) {
                constraints.push_back(Constraint::Equal(e1.clone(), e2.clone()));
            }
            Ok(())
        }

        (TypeUnderConstruction::Struct(n1, _), TypeUnderConstruction::Struct(n2, _)) => {
            if n1 != n2 {
                bail!(UnificationError::StructNameMismatch {
                    left: n1.clone(),
                    right: n2.clone(),
                });
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
                bail!(UnificationError::UnionNameMismatch {
                    left: s1.clone().into(),
                    right: s2.clone().into()
                });
            }
            Ok(())
        }

        (
            TypeUnderConstruction::RecurseMarker(s),
            TypeUnderConstruction::Struct(SymbolOrPlaceholder::Symbol(name), _),
        )
        | (
            TypeUnderConstruction::Struct(SymbolOrPlaceholder::Symbol(name), _),
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
            TypeUnderConstruction::Union(SymbolOrPlaceholder::Symbol(name), _),
        )
        | (
            TypeUnderConstruction::Union(SymbolOrPlaceholder::Symbol(name), _),
            TypeUnderConstruction::RecurseMarker(s),
        ) => {
            if s != name {
                bail!(UnificationError::UnionNameMismatch {
                    left: s.clone().into(),
                    right: name.clone().into()
                });
            }
            Ok(())
        }

        (ty1, ty2) => {
            bail!(UnificationError::IncompatibleTypes {
                left: ty1.clone(),
                right: ty2.clone()
            });
        }
    }
}

fn occurs_check(var: &TypeVar, ty: &TypeUnderConstruction) -> bool {
    match ty {
        TypeUnderConstruction::Var(v) => v == var,
        TypeUnderConstruction::Function(args, ret) => {
            args.iter().any(|arg| occurs_check(var, arg)) || occurs_check(var, ret)
        }
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
        TypeUnderConstruction::Function(args, ret) => TypeUnderConstruction::Function(
            Box::new(apply_substitution_to_args(args, subst)),
            Box::new(apply_substitution(ret, subst)),
        ),
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

fn apply_substitution_to_args(
    args: &LinkedList<TypeUnderConstruction>,
    subst: &Substitution,
) -> LinkedList<TypeUnderConstruction> {
    let (head, tail) = args.peek();
    let head = apply_substitution(head, subst);
    match tail {
        Some(tail) => LinkedList::new(head, apply_substitution_to_args(tail, subst)),
        None => LinkedList::singleton(head),
    }
}
