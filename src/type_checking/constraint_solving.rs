use crate::{
    type_checking::{
        Constraint, StructField, SymbolOrPlaceholder, TypeError, TypeOrVar, TypeUnderConstruction,
        TypeVar, UnionMember,
    },
    util::LinkedList,
};
use anyhow::{Context, Result, bail};
use std::collections::{HashMap, VecDeque};

type Substitution = HashMap<TypeVar, TypeUnderConstruction>;

pub fn solve_constraints(constraints: Vec<Constraint>) -> Result<Substitution> {
    let mut subst = Substitution::new();
    let mut remaining: VecDeque<_> = constraints.into();

    while let Some(constraint) = remaining.pop_front() {
        match constraint {
            Constraint::Equal(ref t1, ref t2) => {
                let t1_applied = apply_substitution_to_typeorvar(t1, &subst);
                let t2_applied = apply_substitution_to_typeorvar(t2, &subst);

                match (t1_applied.clone(), t2_applied.clone()) {
                    (TypeOrVar::Var(v), TypeOrVar::Concrete(ty))
                    | (TypeOrVar::Concrete(ty), TypeOrVar::Var(v)) => {
                        if occurs_check(&v, &ty) {
                            bail!(TypeError::UnconstructableInfiniteType);
                        }
                        subst.insert(v.clone(), ty.clone());

                        // Apply new substitution to remaining constraints
                        remaining = remaining
                            .into_iter()
                            .map(|c| apply_substitution_to_constraint(&c, &subst))
                            .collect();
                    }

                    (TypeOrVar::Concrete(ty1), TypeOrVar::Concrete(ty2)) => {
                        unify(&ty1, &ty2, &mut remaining).with_context(|| {
                            TypeError::IncompatibleTypes {
                                left: ty1.clone(),
                                right: ty2.clone(),
                            }
                        })?;
                    }

                    (TypeOrVar::Var(ty1), TypeOrVar::Var(ty2)) if ty1 == ty2 => {
                        // Same variable, already unified
                    }

                    (TypeOrVar::Var(ty1), TypeOrVar::Var(ty2)) => {
                        // This cannot be resolved jsut yet.
                        if remaining.iter().all(|c| {
                            matches!(c, Constraint::Equal(TypeOrVar::Var(_), TypeOrVar::Var(_)))
                        }) {
                            bail!(TypeError::IncompatibleTypes {
                                left: TypeUnderConstruction::Var(ty1.clone()),
                                right: TypeUnderConstruction::Var(ty2.clone())
                            })
                        }

                        remaining
                            .push_back(Constraint::Equal(TypeOrVar::Var(ty1), TypeOrVar::Var(ty2)));
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
        (TypeUnderConstruction::Var(ty1), TypeUnderConstruction::Var(ty2)) => {
            constraints.push_back(Constraint::Equal(
                TypeOrVar::Var(ty1.clone()),
                TypeOrVar::Var(ty2.clone()),
            ));
            Ok(())
        }

        // Variable substitutions should be handled by the caller
        (TypeUnderConstruction::Var(_), _) | (_, TypeUnderConstruction::Var(_)) => Ok(()),

        (
            TypeUnderConstruction::Function(args1, ret1),
            TypeUnderConstruction::Function(args2, ret2),
        ) => {
            if args1.len() != args2.len() {
                bail!(TypeError::FunctionArityMismatch {
                    expected: args1.len(),
                    found: args2.len()
                });
            }

            for (a1, a2) in args1.iter().zip(args2.iter()) {
                constraints.push_back(Constraint::Equal(
                    TypeOrVar::Concrete(a1.clone()),
                    TypeOrVar::Concrete(a2.clone()),
                ));
            }

            constraints.push_back(Constraint::Equal(
                TypeOrVar::Concrete(ret1.as_ref().clone()),
                TypeOrVar::Concrete(ret2.as_ref().clone()),
            ));
            Ok(())
        }

        (TypeUnderConstruction::Tuple(elems1), TypeUnderConstruction::Tuple(elems2)) => {
            if elems1.len() != elems2.len() {
                bail!(TypeError::TupleSizeMismatch {
                    expected: elems1.len(),
                    found: elems2.len()
                });
            }

            for (e1, e2) in elems1.iter().zip(elems2.iter()) {
                constraints.push_back(Constraint::Equal(
                    TypeOrVar::Concrete(e1.clone()),
                    TypeOrVar::Concrete(e2.clone()),
                ));
            }
            Ok(())
        }

        (TypeUnderConstruction::Struct(n1, _), TypeUnderConstruction::Struct(n2, _)) => {
            if n1 != n2 {
                bail!(TypeError::StructNameMismatch {
                    left: n1.clone(),
                    right: n2.clone(),
                });
            }
            Ok(())
        }

        (TypeUnderConstruction::Union(n1, _), TypeUnderConstruction::Union(n2, _)) => {
            if n1 != n2 {
                bail!(TypeError::UnionNameMismatch {
                    left: n1.clone(),
                    right: n2.clone(),
                });
            }
            Ok(())
        }

        (TypeUnderConstruction::RecurseMarker(s1), TypeUnderConstruction::RecurseMarker(s2)) => {
            if s1 != s2 {
                bail!(TypeError::UnionNameMismatch {
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
                bail!(TypeError::StructNameMismatch {
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
                bail!(TypeError::UnionNameMismatch {
                    left: s.clone().into(),
                    right: name.clone().into()
                });
            }
            Ok(())
        }

        (ty1, ty2) => {
            bail!(TypeError::IncompatibleTypes {
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
        Constraint::Equal(t1, t2) => Constraint::Equal(
            apply_substitution_to_typeorvar(t1, subst),
            apply_substitution_to_typeorvar(t2, subst),
        ),
        Constraint::Subtype(t1, t2) => Constraint::Subtype(
            apply_substitution_to_typeorvar(t1, subst),
            apply_substitution_to_typeorvar(t2, subst),
        ),
    }
}

fn apply_substitution_to_typeorvar(tov: &TypeOrVar, subst: &Substitution) -> TypeOrVar {
    match tov {
        TypeOrVar::Concrete(t) => TypeOrVar::Concrete(apply_substitution(t, subst)),
        TypeOrVar::Var(v) => {
            if let Some(t) = subst.get(v) {
                TypeOrVar::Concrete(apply_substitution(t, subst))
            } else {
                tov.clone()
            }
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
