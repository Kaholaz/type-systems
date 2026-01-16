use crate::{
    ast::{
        Expression, ExpressionValue, NominalType, StructFieldTypeDeclaration, TypeDefinition,
        TypeExpression, TypeValue, UnionValue, Value, VariableDeclaration, VariableName,
    },
    type_checking::{
        PartialType, TypeEnv, TypeFrame,
        check::Check,
        unification::{PartialStructField, PartialUnionMember, UnificationContext},
    },
    util::LinkedList,
};
use anyhow::{Context, Result};
use nonempty::NonEmpty;
use std::{collections::HashMap, rc::Rc};
use thiserror::Error;

#[derive(Debug, Error)]
enum InferError {
    #[error("attempted to call a non-function value of type {0}")]
    CallNonFunction(PartialType),

    #[error("union member `{member}` does not exist on union type")]
    UnknownUnionMember { member: VariableName },

    #[error("attempted to construct singleton union member `{member}` with a value")]
    SingletonWithValue { member: VariableName },

    #[error("union member `{member}` requires a value")]
    MissingUnionValue { member: VariableName },

    #[error("duplicate union case `{case}`")]
    DuplicateUnionCase { case: VariableName },

    #[error("non-exhaustive case expression without default")]
    NonExhaustiveCase,

    #[error("struct field `{field}` does not exist")]
    UnknownStructField { field: VariableName },

    #[error("duplicate struct field `{field}`")]
    DuplicateStructField { field: VariableName },

    #[error("duplicate union member `{member}`")]
    DuplicateUnionMember { member: VariableName },

    #[error("too few fields provided in struct construction")]
    TooFewStructFields,

    #[error("attempted to do case analysis on a non-union type {0}")]
    CaseOnNonUnion(PartialType),

    #[error("attempted to access a struct with non-struct type {0}")]
    AccessNonStruct(PartialType),

    #[error("attempted to construct a struct with non-struct type {0}")]
    ConstructNonStruct(PartialType),

    #[error("attempted to construct a union with non-union type {0}")]
    ConstructNonUnion(PartialType),

    #[error("internal checker invariant violated: {0}")]
    Internal(&'static str),
}

fn call_function(
    env: &TypeEnv,
    ctx: &mut UnificationContext,
    function: PartialType,
    arg: &ExpressionValue,
) -> Result<PartialType> {
    match function {
        PartialType::Function(expected_args) => {
            let (expected_arg, expected_return) = expected_args.pop();

            let expected_return = expected_return
                .ok_or(InferError::Internal("function type without return value"))?;

            let expected_return = if expected_return.len() == 1 {
                expected_return.pop().0
            } else {
                PartialType::Function(expected_return)
            };

            arg.check(env, ctx, expected_arg)
                .context("while checking function argument")?;

            Ok(expected_return)
        }

        PartialType::Var(var) => {
            let arg_var = ctx.new_type_var();
            arg.check(env, ctx, PartialType::Var(arg_var))
                .with_context(|| {
                    format!("while inferring argument type for type variable {}", var)
                })?;
            let arg = ctx
                .find(arg_var)
                .context("while resolving argument type variable")?;
            let return_var = ctx.new_type_var();
            let return_type = ctx
                .find(return_var)
                .context("while resolving return type variable")?;
            let function = PartialType::Function(Box::new(LinkedList::new(
                arg,
                LinkedList::singleton(return_type),
            )));

            ctx.unify_partial(function, PartialType::Var(var))
                .with_context(|| {
                    format!(
                        "while unifying inferred function type with type variable {}",
                        var
                    )
                })?;
            ctx.find(return_var)
                .context("while finding final return type")
        }

        other => Err(InferError::CallNonFunction(other))
            .context("attempted function call on non-function type"),
    }
}

fn construct_union(
    env: &TypeEnv,
    ctx: &mut UnificationContext,
    union_type: PartialType,
    member_value: &UnionValue,
) -> Result<PartialType> {
    let member_name = member_value.name();

    let PartialType::Union(_, union_members) = &union_type else {
        return Err(InferError::ConstructNonUnion(union_type))
            .with_context(|| format!("while constructing union member `{}`", member_name));
    };

    let expected_member = union_members
        .iter()
        .find(|m| m.name() == member_name)
        .ok_or_else(|| InferError::UnknownUnionMember {
            member: member_name.clone(),
        })
        .with_context(|| {
            let available: Vec<_> = union_members.iter().map(|m| m.name()).collect();
            format!("available union members: {:?}", available)
        })?;

    match (expected_member, member_value) {
        (PartialUnionMember::SingletonUnionMember(_), UnionValue::VariableDeclaration(_)) => {
            Err(InferError::SingletonWithValue {
                member: member_name.clone(),
            })
            .context("singleton union members cannot have associated values")
        }

        (PartialUnionMember::SingletonUnionMember(_), UnionValue::VariableName(_)) => {
            Ok(union_type)
        }

        (
            PartialUnionMember::UnionMember(_, expected_type),
            UnionValue::VariableDeclaration(decl),
        ) => {
            decl.variable_definition
                .check(env, ctx, expected_type.clone())
                .with_context(|| {
                    format!("while checking value for union member `{}`", member_name)
                })?;
            Ok(union_type)
        }

        (PartialUnionMember::UnionMember(_, _), UnionValue::VariableName(_)) => {
            Err(InferError::MissingUnionValue {
                member: member_name.clone(),
            })
            .context("union member requires an associated value")
        }
    }
}

fn construct_struct(
    env: &TypeEnv,
    ctx: &mut UnificationContext,
    struct_type: PartialType,
    struct_fields: &Vec<VariableDeclaration>,
) -> Result<PartialType> {
    match &struct_type {
        PartialType::Struct(_, expected_struct_fields) => {
            let mut struct_fields_ = HashMap::new();
            for field in struct_fields {
                if struct_fields_
                    .insert(field.variable_name.clone(), &field.variable_definition)
                    .is_some()
                {
                    return Err(InferError::DuplicateStructField {
                        field: field.variable_name.clone(),
                    })
                    .context("while collecting struct fields for construction");
                };
            }

            let struct_fields = struct_fields_;

            if struct_fields.len() < expected_struct_fields.len() {
                let provided: Vec<_> = struct_fields.keys().collect();
                let expected: Vec<_> = expected_struct_fields.iter().map(|f| &f.name).collect();
                return Err(InferError::TooFewStructFields).with_context(|| {
                    format!(
                        "expected {} fields ({:?}), but got {} fields ({:?})",
                        expected_struct_fields.len(),
                        expected,
                        struct_fields.len(),
                        provided
                    )
                });
            }

            for (struct_field_name, struct_field_expression) in struct_fields {
                let expected_field = expected_struct_fields
                    .iter()
                    .find(|f| f.name == struct_field_name)
                    .expect("Struct field name not present in type");

                struct_field_expression
                    .check(env, ctx, expected_field.field_type.clone())
                    .with_context(|| {
                        format!(
                            "while checking field `{}` with expected type {:?}",
                            struct_field_name, expected_field.field_type
                        )
                    })?;
            }

            Ok(struct_type)
        }
        PartialType::Var(_) => Err(InferError::Internal(
            "Struct type should be fully infered before we check expressions",
        ))
        .context("during struct construction"),
        other => Err(InferError::ConstructNonStruct(other.clone()))
            .context("attempted to construct a non-struct type as a struct"),
    }
}

fn access_struct(struct_type: PartialType, field_name: &VariableName) -> Result<PartialType> {
    match struct_type {
        PartialType::Struct(_, fields) => fields
            .iter()
            .find(|f| &f.name == field_name)
            .map(|f| f.field_type.clone())
            .ok_or_else(|| InferError::UnknownStructField {
                field: field_name.clone(),
            })
            .with_context(|| {
                let available: Vec<_> = fields.iter().map(|f| &f.name).collect();
                format!("available fields: {:?}", available)
            }),

        other => Err(InferError::AccessNonStruct(other))
            .with_context(|| format!("while accessing field `{}`", field_name)),
    }
}

fn unify_cases(
    env: &TypeEnv,
    ctx: &mut UnificationContext,
    union_type: PartialType,
    explicit_cases: &NonEmpty<VariableDeclaration>,
    default_case: &Option<Expression>,
) -> Result<PartialType> {
    let PartialType::Union(_, union_members) = union_type else {
        return Err(InferError::CaseOnNonUnion(union_type))
            .context("case expressions can only be used on union types");
    };

    let mut cases = HashMap::new();
    for case in explicit_cases {
        if cases
            .insert(case.variable_name.clone(), &case.variable_definition)
            .is_some()
        {
            return Err(InferError::DuplicateUnionCase {
                case: case.variable_name.clone(),
            })
            .context("in case expression");
        }

        if !union_members
            .iter()
            .any(|m| m.name() == &case.variable_name)
        {
            let available: Vec<_> = union_members.iter().map(|m| m.name()).collect();
            return Err(InferError::UnknownUnionMember {
                member: case.variable_name.clone(),
            })
            .with_context(|| format!("available union members: {:?}", available));
        }
    }

    if cases.len() < union_members.len() && default_case.is_none() {
        let covered: Vec<_> = cases.keys().collect();
        let all_members: Vec<_> = union_members.iter().map(|m| m.name()).collect();
        let missing: Vec<_> = all_members
            .iter()
            .filter(|m| !covered.contains(m))
            .collect();
        return Err(InferError::NonExhaustiveCase).with_context(|| {
            format!(
                "missing cases for: {:?}. Add these cases or provide a default case.",
                missing
            )
        });
    }

    let result_var = ctx.new_type_var();

    for member in union_members {
        let expected = ctx
            .find(result_var)
            .context("while finding result type for case expression")?;

        match member {
            PartialUnionMember::SingletonUnionMember(name) => {
                let expr = cases
                    .get(&name)
                    .copied()
                    .or(default_case.as_ref())
                    .ok_or(InferError::NonExhaustiveCase)?;

                expr.check(env, ctx, expected).with_context(|| {
                    format!("while checking case for singleton member `{}`", name)
                })?;
            }

            PartialUnionMember::UnionMember(name, arg_ty) => {
                if let Some(expr) = cases.get(&name) {
                    let expected_fn = match expected {
                        PartialType::Function(args) => {
                            PartialType::Function(LinkedList::cons(arg_ty, args))
                        }
                        ret => PartialType::Function(Box::new(LinkedList::new(
                            arg_ty,
                            LinkedList::singleton(ret),
                        ))),
                    };

                    expr.check(env, ctx, expected_fn).with_context(|| {
                        format!("while checking case for union member `{}`", name)
                    })?;
                } else {
                    default_case
                        .as_ref()
                        .ok_or(InferError::NonExhaustiveCase)?
                        .check(env, ctx, expected)
                        .context("while checking default case")?;
                }
            }
        }
    }

    ctx.find(result_var)
        .context("while finding final result type of case expression")
}

pub trait Infer {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType>;
}

impl Infer for TypeDefinition {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType> {
        match self {
            TypeDefinition::NominalType(nominal_type) => nominal_type
                .infer(env, ctx)
                .context("while inferring nominal type definition"),
            TypeDefinition::TypeExpression(type_expression) => type_expression
                .infer(env, ctx)
                .context("while inferring type expression"),
        }
    }
}

impl Infer for NominalType {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType> {
        match self {
            NominalType::StructType(fields) => {
                let mut field_map = HashMap::new();
                for StructFieldTypeDeclaration {
                    field_name,
                    type_expression,
                } in fields
                {
                    let field_type = type_expression.infer(env, ctx).with_context(|| {
                        format!("while inferring type for struct field `{}`", field_name)
                    })?;
                    let prev = field_map.insert(field_name.clone(), field_type);
                    if prev.is_some() {
                        return Err(InferError::DuplicateStructField {
                            field: field_name.clone(),
                        }
                        .into());
                    }
                }

                let fields = field_map
                    .into_iter()
                    .map(|(name, field_type)| PartialStructField { name, field_type })
                    .collect();
                Ok(PartialType::Struct(ctx.new_type_id(), fields))
            }
            NominalType::EnumType(members) => {
                let mut member_map = HashMap::new();
                for member in members {
                    let member_type = member
                        .type_expression
                        .as_ref()
                        .map(|e| {
                            e.infer(env, ctx).with_context(|| {
                                format!(
                                    "while inferring type for union member `{}`",
                                    member.element_name
                                )
                            })
                        })
                        .transpose()?;
                    let prev = member_map.insert(member.element_name.clone(), member_type);
                    if prev.is_some() {
                        return Err(InferError::DuplicateUnionMember {
                            member: member.element_name.clone(),
                        }
                        .into());
                    }
                }

                let members = member_map
                    .into_iter()
                    .map(|(name, member_type)| match member_type {
                        Some(member_type) => PartialUnionMember::UnionMember(name, member_type),
                        None => PartialUnionMember::SingletonUnionMember(name),
                    })
                    .collect();
                Ok(PartialType::Union(ctx.new_type_id(), members))
            }
        }
    }
}

impl Infer for TypeExpression {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType> {
        match self {
            TypeExpression::TypeValue(type_value) => type_value
                .infer(env, ctx)
                .context("while inferring type value"),
            TypeExpression::FunctionType(type_values) => {
                let args = type_values
                    .iter()
                    .enumerate()
                    .map(|(i, t)| {
                        t.infer(env, ctx).with_context(|| {
                            format!("while inferring function type argument at position {}", i)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(PartialType::Function(Box::new(
                    LinkedList::try_from(args)
                        .expect("Type expressions are garanteed to be non-empty"),
                )))
            }
        }
    }
}

impl Infer for TypeValue {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType> {
        match self {
            TypeValue::TypeName(type_name) => env
                .lookup_type(ctx, type_name.clone())
                .with_context(|| format!("while looking up type `{}`", type_name)),
            TypeValue::TypeTuple(elements) => {
                let elements = elements
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        e.infer(env, ctx).with_context(|| {
                            format!("while inferring tuple element at position {}", i)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(PartialType::Tuple(elements))
            }
        }
    }
}

impl Infer for Expression {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType> {
        let (head, mut tail) = self.values.peek();
        let mut out = head
            .infer(env, ctx)
            .context("while inferring head of expression")?;

        let mut call_count = 0;
        while let Some(arguments) = tail {
            let (arg, tail_inner) = arguments.peek();
            tail = tail_inner;
            out = call_function(env, ctx, out, arg)
                .with_context(|| format!("while processing function call #{}", call_count + 1))?;
            call_count += 1;
        }

        Ok(out)
    }
}

impl Infer for ExpressionValue {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType> {
        match self {
            ExpressionValue::FunctionDeclaration(
                StructFieldTypeDeclaration {
                    field_name,
                    type_expression,
                },
                expression_value,
            ) => {
                let arg_id = ctx.new_type_var();
                type_expression
                    .check(env, ctx, PartialType::Var(arg_id))
                    .with_context(|| {
                        format!(
                            "while checking parameter type for function argument `{}`",
                            field_name
                        )
                    })?;

                let mut stack_frame = TypeFrame::new();
                stack_frame.insert(field_name.clone().into(), arg_id);
                let env = TypeEnv::new(Rc::new(stack_frame), env.clone());

                let ret_id = ctx.new_type_var();
                expression_value
                    .check(&env, ctx, PartialType::Var(ret_id))
                    .with_context(|| {
                        format!("while checking function body (parameter: `{}`)", field_name)
                    })?;

                Ok(PartialType::Function(Box::new(LinkedList::new(
                    ctx.find(arg_id)?,
                    LinkedList::singleton(ctx.find(ret_id)?),
                ))))
            }
            ExpressionValue::ValueExpression(value) => value
                .infer(env, ctx)
                .context("while inferring value expression"),
            ExpressionValue::TypeExpression(type_name, spec) => {
                let typ = env.lookup_type(ctx, type_name.clone()).with_context(|| {
                    format!("while looking up type `{}` for construction", type_name)
                })?;
                match spec {
                    crate::ast::Spec::UnionValue(union_value) => {
                        construct_union(env, ctx, typ, union_value).with_context(|| {
                            format!("while constructing union type `{}`", type_name)
                        })
                    }
                    crate::ast::Spec::StructValue(fields) => {
                        construct_struct(env, ctx, typ, fields).with_context(|| {
                            format!("while constructing struct type `{}`", type_name)
                        })
                    }
                }
            }
        }
    }
}

impl Infer for Value {
    fn infer(&self, env: &TypeEnv, ctx: &mut UnificationContext) -> Result<PartialType> {
        match self {
            Value::Variable(variable_name) => env
                .lookup_variable(ctx, variable_name.clone())
                .with_context(|| format!("while looking up variable `{}`", variable_name)),
            Value::Expression(expression) => expression
                .infer(env, ctx)
                .context("while inferring nested expression"),
            Value::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        e.infer(env, ctx).with_context(|| {
                            format!("while inferring tuple element at position {}", i)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(PartialType::Tuple(elements))
            }
            Value::StructAccess(value, field_name) => {
                let typ = value
                    .infer(env, ctx)
                    .context("while inferring type of struct being accessed")?;
                access_struct(typ, field_name)
                    .with_context(|| format!("while accessing struct field `{}`", field_name))
            }
            Value::Case(value, explicit_cases, default_case) => {
                let typ = value
                    .infer(env, ctx)
                    .context("while inferring type of value in case expression")?;
                unify_cases(env, ctx, typ, explicit_cases, default_case)
                    .context("while unifying cases in case expression")
            }
        }
    }
}
