use crate::{
    ast::{FileName, Program, TypeDeclaration, TypeName, VariableDeclaration, VariableName},
    type_checking::{
        check::Check,
        unification::{
            PartialStructField, PartialType, PartialUnionMember, TypeId, TypeVarId,
            UnificationContext,
        },
    },
    util::LinkedList,
};
use anyhow::{Context, Result};
use core::fmt::Display;
use indexmap::IndexMap;
use std::{collections::HashMap, hash::Hash, rc::Rc};
use thiserror::Error;

mod check;
mod infer;
mod unification;

#[derive(Debug, Error)]
pub enum DriverError {
    #[error("type {var} is not fully inferred")]
    UnresolvedType { var: TypeVarId },

    #[error("unknown type {type_name}")]
    UnknownType { type_name: TypeName },

    #[error("unknown variable {variable_name}")]
    UnknownVariable { variable_name: VariableName },

    #[error("duplicate field in struct {field_name}")]
    DuplicateStructField { field_name: VariableName },

    #[error("duplicate field in union {member_name}")]
    DuplicateUnionMember { member_name: VariableName },

    #[error("internal compiler error: {0}")]
    Internal(&'static str),
}

#[derive(Debug, Clone)]
pub enum Type {
    Struct(TypeName, Vec<StructField>),
    Union(TypeName, Vec<UnionMember>),
    Tuple(Vec<Type>),
    Function(Box<LinkedList<Type>>),
    RecursiveMarker(TypeName),
    TypeParameter(TypeVarId),
}

impl Type {
    fn try_from_partial_type(
        ctx: &UnificationContext,
        id_to_type_name: &HashMap<TypeId, TypeName>,
        partial_type: PartialType,
    ) -> Result<Type> {
        match partial_type {
            PartialType::Var(var) => {
                let typ = ctx.find(var)?;
                match typ {
                    PartialType::Union(id, _) | PartialType::Struct(id, _) => {
                        let name =
                            id_to_type_name
                                .get(&id)
                                .cloned()
                                .ok_or(DriverError::Internal(
                                    "struct type variable missing nominal name",
                                ))?;
                        Ok(Type::RecursiveMarker(name.clone()))
                    }
                    PartialType::Var(v) if v == var => Ok(Type::TypeParameter(var)),
                    _ => Err(DriverError::UnresolvedType { var }.into()),
                }
            }

            PartialType::Struct(id, fields) => {
                let name = id_to_type_name
                    .get(&id)
                    .cloned()
                    .ok_or(DriverError::Internal(
                        "struct type variable missing nominal name",
                    ))?;

                let fields = fields
                    .into_iter()
                    .map(|PartialStructField { name, field_type }| {
                        Ok(StructField {
                            name,
                            field_type: Self::try_from_partial_type(
                                ctx,
                                id_to_type_name,
                                field_type,
                            )?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;

                Ok(Type::Struct(name, fields))
            }

            PartialType::Union(id, members) => {
                let name = id_to_type_name
                    .get(&id)
                    .cloned()
                    .ok_or(DriverError::Internal(
                        "union type variable missing nominal name",
                    ))?;

                let members = members
                    .into_iter()
                    .map(|m| match m {
                        PartialUnionMember::SingletonUnionMember(n) => {
                            Ok(UnionMember::SingletonUnionMember(n))
                        }
                        PartialUnionMember::UnionMember(n, t) => Ok(UnionMember::UnionMember(
                            n,
                            Self::try_from_partial_type(ctx, id_to_type_name, t)?,
                        )),
                    })
                    .collect::<Result<Vec<_>>>()?;

                Ok(Type::Union(name, members))
            }

            PartialType::Tuple(elements) => Ok(Type::Tuple(
                elements
                    .into_iter()
                    .map(|e| Self::try_from_partial_type(ctx, id_to_type_name, e))
                    .collect::<Result<_>>()?,
            )),

            PartialType::Function(args) => {
                let args = args
                    .iter()
                    .map(|a| Self::try_from_partial_type(ctx, id_to_type_name, a.clone()))
                    .collect::<Result<Vec<_>>>()?;

                Ok(Type::Function(Box::new(
                    LinkedList::try_from(args)
                        .map_err(|_| DriverError::Internal("empty function type"))?,
                )))
            }
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Struct(type_name, _) => {
                write!(f, "{}{{}}", type_name)
            }
            Self::Union(type_name, _) => {
                write!(f, "{}[]", type_name)
            }
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
            Type::RecursiveMarker(type_name) => write!(f, "<-{}", type_name),
            Type::TypeParameter(var) => write!(f, "T{}", var),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: VariableName,
    pub field_type: Type,
}
#[derive(Debug, Clone)]
pub enum UnionMember {
    SingletonUnionMember(VariableName),
    UnionMember(VariableName, Type),
}

impl UnionMember {
    pub fn name(&self) -> &VariableName {
        match self {
            UnionMember::SingletonUnionMember(symbol) => symbol,
            UnionMember::UnionMember(symbol, _) => symbol,
        }
    }
    pub fn member_type(&self) -> Option<&Type> {
        match self {
            UnionMember::SingletonUnionMember(_) => None,
            UnionMember::UnionMember(_, typ) => Some(typ),
        }
    }
}

#[derive(Debug, Clone, Error)]
pub enum TypeError {
    #[error("Cannot find type in scope")]
    UnableToFindType,
}
pub type TypeFrame = IndexMap<TypeMapSymbol, TypeVarId>;
pub type TypeEnv = LinkedList<Rc<TypeFrame>>;

impl TypeEnv {
    fn lookup(
        &self,
        ctx: &UnificationContext,
        symbol: &TypeMapSymbol,
    ) -> Result<Option<PartialType>> {
        self.iter()
            .find_map(|f| f.get(symbol))
            .map(|s| ctx.find(*s))
            .transpose()
    }

    fn lookup_type(&self, ctx: &UnificationContext, type_name: TypeName) -> Result<PartialType> {
        let key = type_name.clone().into();
        self.lookup(ctx, &key)?
            .ok_or(DriverError::UnknownType { type_name }.into())
    }

    fn lookup_variable(
        &self,
        ctx: &UnificationContext,
        variable_name: VariableName,
    ) -> Result<PartialType> {
        if is_int_literal(&variable_name) {
            return self.lookup_type(ctx, TypeName::new("Int"));
        }

        let key = variable_name.clone().into();
        self.lookup(ctx, &key)?
            .ok_or(DriverError::UnknownVariable { variable_name }.into())
    }
}

fn is_int_literal(variable_name: &VariableName) -> bool {
    variable_name.as_str().parse::<isize>().is_ok()
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeMapSymbol {
    TypeSymbol(TypeName),
    VariableSymbol(VariableName),
}

impl Display for TypeMapSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeSymbol(type_symbol) => write!(f, "{}", type_symbol.as_str()),
            Self::VariableSymbol(variable_symbol) => write!(f, "{}", variable_symbol.as_str()),
        }
    }
}

impl From<VariableName> for TypeMapSymbol {
    fn from(value: VariableName) -> Self {
        TypeMapSymbol::VariableSymbol(value)
    }
}

impl From<TypeName> for TypeMapSymbol {
    fn from(value: TypeName) -> Self {
        TypeMapSymbol::TypeSymbol(value)
    }
}

pub fn type_check(program: &Program) -> Result<Vec<(TypeMapSymbol, Type)>> {
    let mut ctx = UnificationContext::new();
    let mut id_to_type_name = HashMap::new();
    let (out, _) = type_check_impl(&mut ctx, &mut id_to_type_name, &mut Vec::new(), program)?.pop();
    out.iter()
        .map(|(name, var)| {
            Ok((
                name.clone(),
                Type::try_from_partial_type(&ctx, &id_to_type_name, ctx.find(*var)?)?,
            ))
        })
        .collect()
}

pub fn type_check_impl(
    ctx: &mut UnificationContext,
    id_to_type_name: &mut HashMap<TypeId, TypeName>,
    already_imported: &mut Vec<FileName>,
    program: &Program,
) -> Result<TypeEnv> {
    // Insert predefined types
    let mut predefined_frame = TypeFrame::new();
    insert_int_type(ctx, &mut predefined_frame, id_to_type_name);
    let mut env = TypeEnv::singleton(Rc::new(predefined_frame));

    // Collect all type variables
    let mut type_definitions = Vec::new();
    let mut variable_definitions = Vec::new();
    let mut stack_frame = TypeFrame::new();
    for statement in &program.definitions {
        match statement {
            crate::ast::Declaration::IncludeDeclaration(file_name, included_program) => {
                if already_imported.contains(file_name) {
                    continue;
                }
                already_imported.push(file_name.clone());
                let included_types =
                    type_check_impl(ctx, id_to_type_name, already_imported, included_program)
                        .context("while checking included program")?;
                env = included_types.push_back(env);
            }
            crate::ast::Declaration::TypeDeclaration(type_definition) => {
                stack_frame.insert(type_definition.type_name.clone().into(), ctx.new_type_var());
                type_definitions.push(type_definition);
            }
            crate::ast::Declaration::VariableDeclaration(variable_definition) => {
                stack_frame.insert(
                    variable_definition.variable_name.clone().into(),
                    ctx.new_type_var(),
                );
                variable_definitions.push(variable_definition);
            }
        }
    }

    let env = TypeEnv::new(Rc::new(stack_frame), env);
    for TypeDeclaration {
        type_name,
        type_definition,
    } in type_definitions
    {
        let expected = env.lookup_type(ctx, type_name.clone())?;
        if let Some(type_definition) = type_definition.as_ref() {
            type_definition.check(&env, ctx, expected)?;
        } else {
            // leave the type variable unconstrained; it can be inferred through use,
            // and if it remains unconstrained it becomes a type parameter.
        }
        let typ = env.lookup_type(ctx, type_name.clone())?;
        match typ {
            PartialType::Union(id, _) | PartialType::Struct(id, _) => {
                id_to_type_name.insert(id, type_name.clone());
            }
            _ => (),
        }
    }

    for VariableDeclaration {
        variable_name,
        variable_definition,
    } in variable_definitions
    {
        let expected = env.lookup_variable(ctx, variable_name.clone())?;
        variable_definition.check(&env, ctx, expected)?;
    }

    Ok(env)
}

fn insert_int_type(
    ctx: &mut UnificationContext,
    frame: &mut TypeFrame,
    id_to_type_name: &mut HashMap<TypeId, TypeName>,
) {
    let pos_int_var = ctx.new_type_var();
    let pos_int_type_id = ctx.new_type_id();
    let pos_int = PartialType::Union(
        pos_int_type_id,
        vec![
            PartialUnionMember::SingletonUnionMember(VariableName::new("0")),
            PartialUnionMember::UnionMember(
                VariableName::new("pre"),
                PartialType::Var(pos_int_var),
            ),
        ],
    );
    ctx.unify_partial(pos_int, PartialType::Var(pos_int_var))
        .expect("This should run on a fresh environment, thus being deterministic");
    frame.insert(TypeName::new("PosInt").into(), pos_int_var);
    id_to_type_name.insert(pos_int_type_id, TypeName::new("PosInt"));

    let neg_int_var = ctx.new_type_var();
    let neg_int_type_id = ctx.new_type_id();
    let neg_int = PartialType::Union(
        neg_int_type_id,
        vec![
            PartialUnionMember::SingletonUnionMember(VariableName::new("-1")),
            PartialUnionMember::UnionMember(
                VariableName::new("pre"),
                PartialType::Var(neg_int_var),
            ),
        ],
    );
    ctx.unify_partial(neg_int, PartialType::Var(neg_int_var))
        .expect("This should run on a fresh environment, thus being deterministic");
    frame.insert(TypeName::new("NegInt").into(), neg_int_var);
    id_to_type_name.insert(neg_int_type_id, TypeName::new("NegInt"));

    let int_var = ctx.new_type_var();
    let int_type_id = ctx.new_type_id();
    let int = PartialType::Union(
        int_type_id,
        vec![
            PartialUnionMember::UnionMember(
                VariableName::new("pos"),
                PartialType::Var(pos_int_var),
            ),
            PartialUnionMember::UnionMember(
                VariableName::new("neg"),
                PartialType::Var(neg_int_var),
            ),
        ],
    );
    ctx.unify_partial(int, PartialType::Var(int_var))
        .expect("This should run on a fresh environment, thus being deterministic");
    frame.insert(TypeName::new("Int").into(), int_var);
    id_to_type_name.insert(int_type_id, TypeName::new("Int"));
}
