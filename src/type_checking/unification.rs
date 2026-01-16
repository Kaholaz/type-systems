use crate::{
    ast::{TypeName, VariableName},
    type_checking::{StructField, Type, UnionMember},
    util::LinkedList,
};
use anyhow::{Context, Result};
use std::{collections::HashMap, fmt::Display};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum UnificationError {
    #[error("cannot unify incompatible types:\nexpected: {expected}\nactual: {actual}")]
    IncompatibleTypes {
        actual: PartialType,
        expected: PartialType,
    },

    #[error("cannot unify incompatible structs: {left} vs {right}")]
    IncompatibleStructs { left: TypeId, right: TypeId },

    #[error("cannot unify incompatible unions: {left} vs {right}")]
    IncompatibleUnions { left: TypeId, right: TypeId },

    #[error("tuple arity mismatch: expected {expected} elements, found {found} elements")]
    TupleArityMismatch { expected: usize, found: usize },

    #[error(
        "infinite recursive type detected while expanding variable; this type is not constructable\ntype: {typ}"
    )]
    UnconstructableInfiniteType { typ: PartialType },

    #[error(
        "invalid recursive union detected while expanding variable; all unions need a non-recursive case to be constructable"
    )]
    InfiniteUnion { id: TypeId },

    #[error("invalid recursive type detected while expanding variable")]
    InfiniteTypeCycle { var: TypeVarId },
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TypeVarId(usize);

impl Display for TypeVarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TypeId(usize);

impl Display for TypeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "__typevar_{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub enum PartialType {
    Var(TypeVarId),
    Struct(TypeId, Vec<PartialStructField>),
    Union(TypeId, Vec<PartialUnionMember>),
    Tuple(Vec<PartialType>),
    Function(Box<LinkedList<PartialType>>),
}

#[derive(Debug, Clone)]
pub struct PartialStructField {
    pub name: VariableName,
    pub field_type: PartialType,
}

#[derive(Debug, Clone)]
pub enum PartialUnionMember {
    SingletonUnionMember(VariableName),
    UnionMember(VariableName, PartialType),
}

impl PartialType {
    pub fn from_type(
        ctx: &mut UnificationContext,
        id_to_type_name: &mut HashMap<TypeId, TypeName>,
        typ: &Type,
    ) -> Self {
        let mut id_to_type_name_inner = Vec::new();
        let mut unification_goals = Vec::new();
        let typ =
            Self::from_type_impl(ctx, &mut id_to_type_name_inner, &mut unification_goals, typ);

        let typ = match &typ {
            PartialType::Struct(id, _) | PartialType::Union(id, _) => {
                let name = id_to_type_name_inner
                    .iter()
                    .find_map(|(id_inner, type_name)| {
                        if id_inner == id {
                            Some(type_name)
                        } else {
                            None
                        }
                    })
                    .unwrap();

                let recurse_vars = unification_goals.iter().filter_map(|(var, name_inner)| {
                    if name == name_inner { Some(var) } else { None }
                });

                recurse_vars.for_each(|var| {
                    ctx.unify_partial(typ.clone(), PartialType::Var(*var))
                        .unwrap()
                });
                typ
            }
            _ => typ,
        };

        for (id, name) in id_to_type_name_inner {
            id_to_type_name.insert(id, name);
        }
        typ
    }

    fn from_type_impl(
        ctx: &mut UnificationContext,
        id_to_type_name: &mut Vec<(TypeId, TypeName)>,
        unification_goals: &mut Vec<(TypeVarId, TypeName)>,
        typ: &Type,
    ) -> Self {
        match typ {
            Type::Struct(type_name, struct_fields) => {
                let type_id = ctx.new_type_id();
                id_to_type_name.push((type_id, type_name.clone()));
                let fields = struct_fields
                    .iter()
                    .map(|StructField { name, field_type }| PartialStructField {
                        name: name.clone(),
                        field_type: PartialType::from_type_impl(
                            ctx,
                            id_to_type_name,
                            unification_goals,
                            field_type,
                        ),
                    })
                    .collect();
                PartialType::Struct(type_id, fields)
            }
            Type::Union(type_name, union_members) => {
                let type_id = ctx.new_type_id();
                id_to_type_name.push((type_id, type_name.clone()));
                let members = union_members
                    .iter()
                    .map(|member| match member {
                        UnionMember::SingletonUnionMember(name) => {
                            PartialUnionMember::SingletonUnionMember(name.clone())
                        }
                        UnionMember::UnionMember(name, typ) => PartialUnionMember::UnionMember(
                            name.clone(),
                            PartialType::from_type_impl(
                                ctx,
                                id_to_type_name,
                                unification_goals,
                                typ,
                            ),
                        ),
                    })
                    .collect();
                PartialType::Union(type_id, members)
            }
            Type::Tuple(elements) => PartialType::Tuple(
                elements
                    .iter()
                    .map(|e| {
                        PartialType::from_type_impl(ctx, id_to_type_name, unification_goals, e)
                    })
                    .collect(),
            ),
            Type::Function(args) => {
                let args = args.map_to_owned(|arg| {
                    PartialType::from_type_impl(ctx, id_to_type_name, unification_goals, arg)
                });
                PartialType::Function(Box::new(args))
            }
            Type::RecursiveMarker(type_name) => {
                let var = ctx.new_type_var();
                unification_goals.push((var, type_name.clone()));
                PartialType::Var(var)
            }
        }
    }
}

impl Display for PartialType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Struct(id, _) => write!(f, "{}", id),
            Self::Union(id, _) => write!(f, "{}", id),
            Self::Tuple(elms) => {
                write!(
                    f,
                    "({})",
                    elms.iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::Function(args) => {
                write!(
                    f,
                    "({})",
                    args.iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(" -> "),
                )
            }
            Self::Var(var) => {
                write!(f, "__typevar_{}", var)
            }
        }
    }
}

impl PartialUnionMember {
    pub fn name(&self) -> &VariableName {
        match self {
            PartialUnionMember::SingletonUnionMember(symbol) => symbol,
            PartialUnionMember::UnionMember(symbol, _) => symbol,
        }
    }
}

impl Eq for PartialType {}

impl PartialEq for PartialType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Struct(l0, _), Self::Struct(r0, _)) => l0 == r0,
            (Self::Union(l0, _), Self::Union(r0, _)) => l0 == r0,
            (Self::Tuple(l0), Self::Tuple(r0)) => l0 == r0,
            (Self::Function(l0), Self::Function(r0)) => {
                l0.len() == r0.len() && l0.iter().zip(r0.iter()).all(|(a, b)| a == b)
            }
            (Self::Var(l0), Self::Var(r0)) => l0 == r0,
            _ => false,
        }
    }
}

#[derive(Clone, Default)]
struct ExpandContext {
    visiting_vars: Vec<TypeVarId>,
    visiting_nominals: Vec<TypeId>,
}

pub struct UnificationContext {
    map: HashMap<TypeVarId, PartialType>,
    counter: usize,
}

impl UnificationContext {
    pub fn new() -> Self {
        UnificationContext {
            map: HashMap::new(),
            counter: usize::default(),
        }
    }

    pub fn new_type_var(&mut self) -> TypeVarId {
        let var = TypeVarId(self.counter);
        self.counter += 1;
        self.map.insert(var, PartialType::Var(var));
        var
    }

    pub fn new_type_id(&mut self) -> TypeId {
        let var = TypeId(self.counter);
        self.counter += 1;
        var
    }

    pub fn find(&self, var: TypeVarId) -> Result<PartialType> {
        self.expand(PartialType::Var(var))
    }

    pub fn expand(&self, ty: PartialType) -> Result<PartialType> {
        let (typ, bounded) = self.expand_inner(ty, &mut ExpandContext::default())?;
        if !bounded {
            Err(UnificationError::UnconstructableInfiniteType { typ }.into())
        } else {
            Ok(typ)
        }
    }

    fn expand_inner(
        &self,
        ty: PartialType,
        ctx: &mut ExpandContext,
    ) -> Result<(PartialType, bool)> {
        match ty {
            PartialType::Var(v) => {
                if ctx.visiting_vars.contains(&v) {
                    return Err(UnificationError::InfiniteTypeCycle { var: v }.into());
                }

                ctx.visiting_vars.push(v);
                let res = match self.map.get(&v) {
                    Some(inner) if inner == &PartialType::Var(v) => (PartialType::Var(v), true),
                    Some(inner) => self
                        .expand_inner(inner.clone(), ctx)
                        .with_context(|| format!("expanding type var {}", v))?,
                    None => (PartialType::Var(v), true),
                };
                ctx.visiting_vars.pop();

                Ok(res)
            }

            PartialType::Struct(id, fields) => {
                if ctx.visiting_nominals.contains(&id) {
                    return Ok((PartialType::Struct(id, vec![]), false));
                }

                ctx.visiting_nominals.push(id);

                let mut child_ctx = ExpandContext {
                    visiting_vars: Vec::new(),
                    visiting_nominals: ctx.visiting_nominals.clone(),
                };

                let mut is_struct_bounded = true; // Assume true until proven otherwise
                let expanded_fields = fields
                    .into_iter()
                    .map(|f| {
                        let (ty, field_bounded) =
                            self.expand_inner(f.field_type, &mut child_ctx)?;

                        if !field_bounded {
                            is_struct_bounded = false;
                        }

                        Ok(PartialStructField {
                            name: f.name,
                            field_type: ty,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;

                ctx.visiting_nominals.pop();

                Ok((PartialType::Struct(id, expanded_fields), is_struct_bounded))
            }

            PartialType::Union(id, members) => {
                if ctx.visiting_nominals.contains(&id) {
                    return Ok((PartialType::Union(id, vec![]), false));
                }

                ctx.visiting_nominals.push(id);
                let mut child_ctx = ExpandContext {
                    visiting_vars: Vec::new(),
                    visiting_nominals: ctx.visiting_nominals.clone(),
                };

                let mut is_union_bounded = false;
                let expanded_members = members
                    .into_iter()
                    .map(|m| match m {
                        PartialUnionMember::SingletonUnionMember(n) => {
                            is_union_bounded = true; // Base case found!
                            Ok(PartialUnionMember::SingletonUnionMember(n))
                        }
                        PartialUnionMember::UnionMember(n, t) => {
                            let (ty, bounded) = self.expand_inner(t, &mut child_ctx)?;
                            if bounded {
                                is_union_bounded = true;
                            }
                            Ok(PartialUnionMember::UnionMember(n, ty))
                        }
                    })
                    .collect::<Result<Vec<_>>>()?;
                ctx.visiting_nominals.pop();

                if !is_union_bounded {
                    return Err(UnificationError::InfiniteUnion { id }.into());
                }

                Ok((PartialType::Union(id, expanded_members), true))
            }

            PartialType::Tuple(elems) => {
                let expanded_elems = elems
                    .into_iter()
                    .map(|e| self.expand_inner(e, ctx).map(|(t, _)| t))
                    .collect::<Result<Vec<_>>>()?;
                Ok((PartialType::Tuple(expanded_elems), true))
            }

            PartialType::Function(args) => {
                let expanded_args = args
                    .iter()
                    .cloned() // Clone needed if Box<[Type]>
                    .map(|a| self.expand_inner(a, ctx).map(|(t, _)| t))
                    .collect::<Result<Vec<_>>>()?;
                Ok((
                    PartialType::Function(Box::new(expanded_args.try_into().unwrap())),
                    true,
                ))
            }
        }
    }

    pub fn unify_vars(&mut self, inferred: TypeVarId, expected: TypeVarId) -> Result<()> {
        let inferred_type = self
            .find(inferred)
            .with_context(|| format!("while resolving inferred type variable {}", inferred))?;
        let expected_type = self
            .find(expected)
            .with_context(|| format!("while resolving expected type variable {}", expected))?;

        match (inferred_type, expected_type) {
            (PartialType::Var(a), PartialType::Var(b)) if a == b => Ok(()),

            (inferred, PartialType::Var(expected_var)) => {
                self.map.insert(expected_var, inferred);
                Ok(())
            }

            (PartialType::Var(inferred_var), other) => Err(UnificationError::IncompatibleTypes {
                actual: PartialType::Var(inferred_var),
                expected: other,
            })
            .with_context(|| {
                format!(
                    "while unifying type variables: inferred variable {} vs expected type",
                    inferred_var
                )
            }),

            (inferred, expected) => {
                let inferred_str = inferred.to_string();
                let expected_str = expected.to_string();
                self.unify_partial(inferred, expected).with_context(|| {
                    format!(
                        "while unifying type variables {} and {}",
                        inferred_str, expected_str
                    )
                })
            }
        }
    }

    pub fn unify_partial(&mut self, inferred: PartialType, expected: PartialType) -> Result<()> {
        match (inferred, expected) {
            (PartialType::Var(a), PartialType::Var(b)) => self
                .unify_vars(a, b)
                .with_context(|| format!("while unifying type variables {} and {}", a, b)),
            (partial, PartialType::Var(v)) | (PartialType::Var(v), partial) => {
                self.map.insert(v, partial.clone());
                Ok(())
            }

            (
                PartialType::Function(mut inferred_args),
                PartialType::Function(mut expected_args),
            ) => {
                let inferred_arity = inferred_args.len();
                let expected_arity = expected_args.len();

                // assume expected_args.len >= inferred_args.len()
                if inferred_args.len() < expected_args.len() {
                    return self
                        .unify_partial(
                            PartialType::Function(expected_args),
                            PartialType::Function(inferred_args),
                        )
                        .context("while unifying function types (reversed for arity)");
                }

                let mut arg_position = 0;
                while expected_args.len() > 1 {
                    let (expected_arg, expected_args_inner) = expected_args.pop();
                    expected_args = expected_args_inner.unwrap();
                    let (inferred_arg, inferred_args_inner) = inferred_args.pop();
                    inferred_args = inferred_args_inner.unwrap();

                    let inferred_arg_str = inferred_arg.to_string();
                    let expected_arg_str = expected_arg.to_string();
                    self.unify_partial(inferred_arg, expected_arg)
                        .with_context(|| {
                            format!(
                                "while unifying function argument at position {}:\n  expected: {}\n  actual:   {}",
                                arg_position, expected_arg_str, inferred_arg_str
                            )
                        })?;
                    arg_position += 1;
                }

                let expected_return = expected_args.pop().0;
                let inferred_return = if inferred_args.len() == 1 {
                    inferred_args.pop().0
                } else {
                    PartialType::Function(inferred_args)
                };

                let expected_return_string = expected_return.to_string();
                let inferred_return_string = inferred_return.to_string();
                self.unify_partial(inferred_return, expected_return)
                    .with_context(|| {
                        format!(
                            "while unifying function return type:\n  expected: {}\n  actual:   {}",
                            expected_return_string, inferred_return_string
                        )
                    })
                    .with_context(|| {
                        format!(
                            "while unifying function types (inferred arity: {}, expected arity: {})",
                            inferred_arity, expected_arity
                        )
                    })
            }
            (PartialType::Struct(a, fields_a), PartialType::Struct(b, fields_b)) => {
                if a == b {
                    Ok(())
                } else {
                    let fields_a_str: Vec<_> =
                        fields_a.iter().map(|f| f.name.to_string()).collect();
                    let fields_b_str: Vec<_> =
                        fields_b.iter().map(|f| f.name.to_string()).collect();
                    Err(UnificationError::IncompatibleStructs { left: a, right: b }).with_context(
                        || {
                            format!(
                                "struct {} has fields [{}], struct {} has fields [{}]",
                                a,
                                fields_a_str.join(", "),
                                b,
                                fields_b_str.join(", ")
                            )
                        },
                    )
                }
            }

            (PartialType::Union(a, members_a), PartialType::Union(b, members_b)) => {
                if a == b {
                    Ok(())
                } else {
                    let members_a_str: Vec<_> =
                        members_a.iter().map(|m| m.name().to_string()).collect();
                    let members_b_str: Vec<_> =
                        members_b.iter().map(|m| m.name().to_string()).collect();
                    Err(UnificationError::IncompatibleUnions { left: a, right: b }).with_context(
                        || {
                            format!(
                                "union {} has members [{}], union {} has members [{}]",
                                a,
                                members_a_str.join(", "),
                                b,
                                members_b_str.join(", ")
                            )
                        },
                    )
                }
            }

            (PartialType::Tuple(a), PartialType::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(UnificationError::TupleArityMismatch {
                        expected: b.len(),
                        found: a.len(),
                    })
                    .with_context(|| {
                        format!(
                            "expected tuple ({}), found tuple ({})",
                            b.iter()
                                .map(|t| t.to_string())
                                .collect::<Vec<_>>()
                                .join(", "),
                            a.iter()
                                .map(|t| t.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    });
                }

                for (i, (x, y)) in a.into_iter().zip(b.into_iter()).enumerate() {
                    let x_str = x.to_string();
                    let y_str = y.to_string();
                    self.unify_partial(x, y)
                        .with_context(|| {
                            format!(
                                "while unifying tuple element at position {}:\n  expected: {}\n  actual:   {}",
                                i, y_str, x_str
                            )
                        })?;
                }

                Ok(())
            }

            (left, right) => Err(UnificationError::IncompatibleTypes {
                actual: left.clone(),
                expected: right.clone(),
            })
            .with_context(|| {
                format!(
                    "cannot unify {} with {}",
                    type_kind_name(&left),
                    type_kind_name(&right)
                )
            }),
        }
    }
}

impl Default for UnificationContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper function to get a human-readable name for the kind of type
fn type_kind_name(ty: &PartialType) -> &'static str {
    match ty {
        PartialType::Var(_) => "type variable",
        PartialType::Struct(_, _) => "struct type",
        PartialType::Union(_, _) => "union type",
        PartialType::Tuple(_) => "tuple type",
        PartialType::Function(_) => "function type",
    }
}
