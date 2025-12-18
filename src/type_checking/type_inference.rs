use crate::{
    ast::{
        Declaration, EnumElementTypeDeclaration, Expression, ExpressionValue, NominalType, Program,
        Spec, StructFieldTypeDeclaration, TypeDeclaration, TypeDefinition, TypeExpression,
        TypeValue, UnionValue, Value, VariableDeclaration,
    },
    type_checking::{
        Constraint, ConstraintContext, StructField, SymbolOrPlaceholder, TypeMapSymbol, TypeSymbol,
        TypeUnderConstruction, UnionMember, VariableSymbol,
    },
    util::LinkedList,
};
use anyhow::{Context, Result, bail};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug, Clone)]
pub enum TypeInferenceError {
    #[error("Unknown variable '{0:?}' - variable not found in current scope or any parent scope")]
    UnknownVariable(VariableSymbol),

    #[error("Unknown type '{0}' - type not declared or not in scope")]
    UnknownType(TypeSymbol),

    #[error("Duplicate variable definition '{0:?}' - variable already defined in this scope")]
    DuplicateVariableDefinition(VariableSymbol),

    #[error("Duplicate type definition '{0}' - type already defined in this scope")]
    DuplicateTypeDefinition(TypeSymbol),

    #[error(
        "Illegal function arity - attempted to call a non-function value or provided wrong number of arguments"
    )]
    IllegalArity,

    #[error("Struct field '{0:?}' does not exist on this struct type")]
    StructFieldDoesNotExist(VariableSymbol),

    #[error(
        "Attempted to access field on a non-struct type - only struct types support field access"
    )]
    StructAccessOfNonStruct,

    #[error(
        "Not all required struct fields were specified - missing one or more field initializers"
    )]
    NotAllStructFieldsSpecified,

    #[error("Union variant '{0:?}' does not exist on this union type")]
    VariantDoesNotExist(VariableSymbol),

    #[error("Cannot construct type - type definition and initializer structure are incompatible")]
    CannotConstruct,

    #[error("Pattern match (case) expression must be performed on a Union type, not other types")]
    CasesOfNonUnionType,

    #[error(
        "Pattern match incomplete - variant '{0:?}' is not handled and no default case provided"
    )]
    CaseNotCovered(VariableSymbol),
}

type TypeFrame = HashMap<TypeMapSymbol, TypeUnderConstruction>;

#[derive(Debug)]
struct TypeStack<'a> {
    frame: TypeFrame,
    prev: Option<&'a TypeStack<'a>>,
}

fn lookup_symbol<'a>(
    stack: &'a TypeStack,
    symbol: &TypeMapSymbol,
) -> Result<&'a TypeUnderConstruction> {
    let TypeStack { frame, prev } = stack;
    match frame.get(symbol) {
        Some(t) => Ok(t),
        None => match prev {
            Some(prev) => lookup_symbol(prev, symbol)
                .with_context(|| format!("While searching parent scopes for symbol {:?}", symbol)),
            None => match symbol {
                TypeMapSymbol::VariableSymbol(v) => {
                    bail!(TypeInferenceError::UnknownVariable(v.clone()))
                }
                TypeMapSymbol::TypeSymbol(t) => bail!(TypeInferenceError::UnknownType(t.clone())),
            },
        },
    }
}

fn insert(frame: &mut TypeFrame, k: TypeMapSymbol, v: TypeUnderConstruction) -> Result<()> {
    if frame.contains_key(&k) {
        match k {
            TypeMapSymbol::VariableSymbol(v) => {
                bail!(TypeInferenceError::DuplicateVariableDefinition(v))
            }
            TypeMapSymbol::TypeSymbol(t) => bail!(TypeInferenceError::DuplicateTypeDefinition(t)),
        };
    }
    frame.insert(k, v);
    Ok(())
}

pub fn generate_constraints(program: &Program) -> Result<(TypeFrame, Vec<Constraint>)> {
    let mut frame = TypeFrame::new();
    let mut ctx = ConstraintContext::new();

    // First pass: register all top-level declarations
    for definition in &program.definitions {
        match definition {
            Declaration::TypeDeclaration(TypeDeclaration { type_name, .. }) => {
                insert(
                    &mut frame,
                    type_name.clone().into(),
                    TypeUnderConstruction::RecurseMarker(type_name.clone().into()),
                )
                .with_context(|| format!("While registering type declaration '{}'", type_name))?;
            }
            Declaration::VariableDeclaration(VariableDeclaration { variable_name, .. }) => {
                let var = ctx.fresh_var();
                insert(
                    &mut frame,
                    variable_name.clone().into(),
                    TypeUnderConstruction::Var(var),
                )
                .with_context(|| {
                    format!(
                        "While registering variable declaration '{:?}'",
                        variable_name
                    )
                })?;
            }
            _ => {}
        }
    }

    let mut stack = TypeStack { frame, prev: None };

    // Second pass: infer types for all declarations
    for definition in &program.definitions {
        match &definition {
            Declaration::IncludeDeclaration(_) => todo!(),
            &Declaration::TypeDeclaration(type_declaration) => {
                let TypeDeclaration {
                    type_name,
                    type_definition,
                } = type_declaration;

                let ty = match type_definition
                    .type_infer(&stack, &mut ctx)
                    .with_context(|| {
                        format!("While inferring type definition for '{}'", type_name)
                    })? {
                    TypeUnderConstruction::Struct(_, fields) => {
                        TypeUnderConstruction::Struct(type_name.clone().into(), fields)
                    }
                    TypeUnderConstruction::Union(_, members) => {
                        TypeUnderConstruction::Union(type_name.clone().into(), members)
                    }
                    ty => ty,
                };

                stack.frame.insert(type_name.clone().into(), ty);
            }
            Declaration::VariableDeclaration(variable_declaration) => {
                let VariableDeclaration {
                    variable_name,
                    variable_definition,
                } = variable_declaration;

                let var_type = stack
                    .frame
                    .get(&variable_name.clone().into())
                    .unwrap()
                    .clone();

                let inferred_type = variable_definition
                    .type_infer(&stack, &mut ctx)
                    .with_context(|| {
                        format!("While inferring type for variable '{:?}'", variable_name)
                    })?;

                ctx.add_constraint(Constraint::Equal(var_type.clone(), inferred_type.clone()));

                stack
                    .frame
                    .insert(variable_name.clone().into(), inferred_type);
            }
        }
    }

    Ok((stack.frame, ctx.constraints))
}

trait TypeInfer {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction>;
}

impl TypeInfer for TypeDefinition {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction> {
        match self {
            TypeDefinition::NominalType(nominal_type) => nominal_type
                .type_infer(stack, ctx)
                .context("While inferring nominal type"),
            TypeDefinition::TypeExpression(tyexpression) => tyexpression
                .type_infer(stack, ctx)
                .context("While inferring type expression"),
        }
    }
}

impl TypeInfer for NominalType {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction> {
        match self {
            NominalType::StructType(ast_fields) => {
                let mut fields = Vec::new();
                for field in ast_fields {
                    let StructFieldTypeDeclaration {
                        field_name,
                        type_expression,
                    } = field;

                    let struct_field = StructField {
                        name: field_name.clone().into(),
                        field_type: type_expression.type_infer(stack, ctx).with_context(|| {
                            format!("While inferring type for struct field '{:?}'", field_name)
                        })?,
                    };
                    fields.push(struct_field);
                }
                Ok(TypeUnderConstruction::Struct(
                    SymbolOrPlaceholder::Placeholder,
                    fields,
                ))
            }
            NominalType::EnumType(ast_members) => {
                let mut members = Vec::new();
                for member in ast_members {
                    let EnumElementTypeDeclaration {
                        element_name,
                        type_expression,
                    } = member;

                    let member = match type_expression {
                        Some(member_type) => UnionMember::UnionMember(
                            element_name.clone().into(),
                            member_type.type_infer(stack, ctx).with_context(|| {
                                format!(
                                    "While inferring type for union variant '{:?}'",
                                    element_name
                                )
                            })?,
                        ),
                        None => UnionMember::SingletonUnionMember(element_name.clone().into()),
                    };
                    members.push(member)
                }
                Ok(TypeUnderConstruction::Union(
                    SymbolOrPlaceholder::Placeholder,
                    members,
                ))
            }
        }
    }
}

impl TypeInfer for TypeExpression {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction> {
        match self {
            TypeExpression::TypeValue(tyvalue) => tyvalue
                .type_infer(stack, ctx)
                .context("While inferring type value"),
            TypeExpression::FunctionType(arguments, return_type) => {
                let arguments = type_infer_arguments(arguments, stack, ctx)
                    .context("While inferring function argument types")?;
                let return_type = return_type
                    .type_infer(stack, ctx)
                    .context("While inferring function return type")?;
                Ok(TypeUnderConstruction::Function(
                    arguments,
                    Box::new(return_type),
                ))
            }
        }
    }
}

fn type_infer_arguments(
    arguments: &LinkedList<TypeValue>,
    stack: &TypeStack,
    ctx: &mut ConstraintContext,
) -> Result<Box<LinkedList<TypeUnderConstruction>>> {
    let (arg, next) = arguments.peek();
    let arg = arg
        .type_infer(stack, ctx)
        .context("While inferring argument type in function signature")?;
    match next {
        Some(next) => {
            let next = type_infer_arguments(next, stack, ctx)?;
            Ok(LinkedList::cons(arg, next))
        }
        None => Ok(Box::new(LinkedList::singleton(arg))),
    }
}

impl TypeInfer for TypeValue {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction> {
        match self {
            TypeValue::TypeName(tyname) => lookup_symbol(stack, &(tyname.clone().into()))
                .with_context(|| format!("While looking up type name '{}'", tyname))
                .cloned(),
            TypeValue::TypeTuple(tuple_members) => {
                let tuple_members = tuple_members
                    .iter()
                    .enumerate()
                    .map(|(i, m)| {
                        m.type_infer(stack, ctx).with_context(|| {
                            format!("While inferring type for tuple element at index {}", i)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TypeUnderConstruction::Tuple(tuple_members))
            }
        }
    }
}

impl TypeInfer for Expression {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction> {
        let (function, args) = self.values.peek();
        let mut value = function
            .type_infer(stack, ctx)
            .context("While inferring type of function expression")?;

        for (i, arg) in args.iter().flat_map(|args| args.iter()).enumerate() {
            let arg = arg.type_infer(stack, ctx).with_context(|| {
                format!("While inferring type of argument {} in function call", i)
            })?;
            value = type_infer_function_call(value, arg, stack, ctx)
                .with_context(|| format!("While applying argument {} to function", i))?;
        }
        Ok(value)
    }
}

fn type_infer_function_call(
    function: TypeUnderConstruction,
    argument: TypeUnderConstruction,
    _stack: &TypeStack,
    ctx: &mut ConstraintContext,
) -> Result<TypeUnderConstruction> {
    match function {
        TypeUnderConstruction::Var(_) => {
            let arg_var = ctx.fresh_var();
            let ret_var = ctx.fresh_var();
            ctx.add_constraint(Constraint::Equal(
                function,
                TypeUnderConstruction::Function(
                    Box::new(LinkedList::singleton(TypeUnderConstruction::Var(
                        arg_var.clone(),
                    ))),
                    Box::new(TypeUnderConstruction::Var(ret_var.clone())),
                ),
            ));
            ctx.add_constraint(Constraint::Subtype(
                argument,
                TypeUnderConstruction::Var(arg_var),
            ));
            Ok(TypeUnderConstruction::Var(ret_var))
        }
        TypeUnderConstruction::Function(argument_types, return_type) => {
            let (argument_type, argument_types) = argument_types.pop();
            ctx.add_constraint(Constraint::Subtype(argument, argument_type));
            match argument_types {
                Some(argument_types) => {
                    Ok(TypeUnderConstruction::Function(argument_types, return_type))
                }
                None => Ok(*return_type),
            }
        }
        _ => bail!(TypeInferenceError::IllegalArity),
    }
}

impl TypeInfer for ExpressionValue {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction> {
        match self {
            ExpressionValue::FunctionDeclaration(declaration, function_body) => {
                let StructFieldTypeDeclaration {
                    field_name: argument_name,
                    type_expression: argument_type,
                } = declaration;

                let mut frame = TypeFrame::new();
                let argument_type = argument_type.type_infer(stack, ctx).with_context(|| {
                    format!(
                        "While inferring type for function parameter '{:?}'",
                        argument_name
                    )
                })?;
                frame.insert(argument_name.clone().into(), argument_type.clone());

                let stack = &TypeStack {
                    frame,
                    prev: Some(stack),
                };

                let return_type = function_body
                    .type_infer(stack, ctx)
                    .context("While inferring type of function body")?;

                let out = match return_type {
                    TypeUnderConstruction::Function(args, return_type) => {
                        TypeUnderConstruction::Function(
                            LinkedList::cons(argument_type, args),
                            return_type,
                        )
                    }
                    _ => TypeUnderConstruction::Function(
                        Box::new(LinkedList::singleton(argument_type)),
                        Box::new(return_type),
                    ),
                };
                Ok(out)
            }
            ExpressionValue::ValueExpression(value) => value
                .type_infer(stack, ctx)
                .context("While inferring type of value expression"),
            ExpressionValue::TypeExpression(tyname, spec) => {
                let ty = lookup_symbol(stack, &tyname.clone().into()).with_context(|| {
                    format!("While looking up type '{}' for construction", tyname)
                })?;

                match (ty, spec) {
                    (
                        TypeUnderConstruction::Struct(struct_name, tyfields),
                        Spec::StructValue(spec_fields),
                    ) => {
                        let mut spec = Vec::new();
                        for VariableDeclaration {
                            variable_name,
                            variable_definition,
                        } in spec_fields
                        {
                            let field = StructField {
                                name: variable_name.clone().into(),
                                field_type: variable_definition.type_infer(stack, ctx)
                                    .with_context(|| format!("While inferring type for struct field '{:?}' in constructor", variable_name))?,
                            };
                            spec.push(field)
                        }

                        let all_fields_are_present =
                            tyfields.iter().all(|StructField { name, field_type }| {
                                let spec_type = spec.iter().find(|sf| &sf.name == name);
                                if let Some(spec_type) = spec_type {
                                    ctx.add_constraint(Constraint::Subtype(
                                        spec_type.field_type.clone(),
                                        field_type.clone(),
                                    ));
                                    true
                                } else {
                                    false
                                }
                            });

                        if all_fields_are_present {
                            Ok(ty.clone())
                        } else {
                            Err(TypeInferenceError::NotAllStructFieldsSpecified).with_context(
                                || format!("While constructing struct type '{:?}'", struct_name),
                            )?
                        }
                    }
                    (
                        TypeUnderConstruction::Union(union_name, union_members),
                        Spec::UnionValue(union_value),
                    ) => {
                        let (spec_name, spec_type) = match union_value {
                            UnionValue::VariableDeclaration(VariableDeclaration {
                                variable_name,
                                variable_definition,
                            }) => (
                                variable_name.clone().into(),
                                Some(variable_definition.type_infer(stack, ctx).with_context(
                                    || {
                                        format!(
                                            "While inferring type for union variant '{:?}' payload",
                                            variable_name
                                        )
                                    },
                                )?),
                            ),
                            UnionValue::VariableName(variable_name) => {
                                (variable_name.clone().into(), None)
                            }
                        };

                        let union_member = union_members.iter().find(|m| m.name() == &spec_name);
                        match union_member {
                            None => Err(TypeInferenceError::VariantDoesNotExist(spec_name.clone()))
                                .with_context(|| format!("While constructing union type '{:?}'", union_name))?,
                            Some(union_member) => match (union_member.member_type(), spec_type) {
                                (None, None) => Ok(ty.clone()),
                                (Some(union_member_type), Some(spec_type)) => {
                                    ctx.add_constraint(Constraint::Subtype(
                                        spec_type,
                                        union_member_type.clone(),
                                    ));
                                    Ok(ty.clone())
                                }
                                (_, _) => Err(TypeInferenceError::CannotConstruct)
                                    .with_context(|| format!("Mismatch between union variant '{:?}' definition and provided value", spec_name))?,
                            },
                        }
                    }
                    _ => bail!(TypeInferenceError::CannotConstruct),
                }
            }
        }
    }
}

impl TypeInfer for Value {
    fn type_infer(
        &self,
        stack: &TypeStack,
        ctx: &mut ConstraintContext,
    ) -> Result<TypeUnderConstruction> {
        match self {
            Value::Variable(variable_name) => lookup_symbol(stack, &variable_name.clone().into())
                .with_context(|| format!("While looking up variable '{:?}'", variable_name))
                .cloned(),
            Value::Expression(expression) => expression
                .type_infer(stack, ctx)
                .context("While inferring type of nested expression"),
            Value::Tuple(elements) => elements
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    e.type_infer(stack, ctx).with_context(|| {
                        format!("While inferring type for tuple element at position {}", i)
                    })
                })
                .collect::<Result<Vec<_>, _>>()
                .map(TypeUnderConstruction::Tuple),
            Value::StructAccess(value, variable_name) => {
                let value = value
                    .type_infer(stack, ctx)
                    .context("While inferring type of struct being accessed")?;

                let fields = match value {
                    TypeUnderConstruction::Struct(_, fields) => Ok(fields),
                    TypeUnderConstruction::RecurseMarker(s) => {
                        match lookup_symbol(stack, &s.into())? {
                            TypeUnderConstruction::Struct(_, fields) => Ok(fields.clone()),
                            _ => Err(TypeInferenceError::StructAccessOfNonStruct),
                        }
                    }
                    _ => Err(TypeInferenceError::StructAccessOfNonStruct),
                }
                .with_context(|| {
                    format!("While attempting to access field '{:?}'", variable_name)
                })?;

                match fields
                    .iter()
                    .find(|&f| f.name == variable_name.clone().into())
                {
                    Some(field) => Ok(field.field_type.clone()),
                    None => Err(TypeInferenceError::StructFieldDoesNotExist(
                        variable_name.clone().into(),
                    ))
                    .with_context(|| {
                        format!(
                            "Available fields: {:?}",
                            fields.iter().map(|f| &f.name).collect::<Vec<_>>()
                        )
                    })?,
                }
            }
            Value::Case(value, explicit_cases_ast, default_case) => {
                let value = value
                    .type_infer(stack, ctx)
                    .context("While inferring type of value being pattern matched")?;

                let members = match value {
                    TypeUnderConstruction::Union(_, members) => Ok(members),
                    TypeUnderConstruction::RecurseMarker(s) => {
                        match lookup_symbol(stack, &s.into())? {
                            TypeUnderConstruction::Union(_, members) => Ok(members.clone()),
                            _ => Err(TypeInferenceError::CasesOfNonUnionType),
                        }
                    }
                    _ => Err(TypeInferenceError::CasesOfNonUnionType),
                }
                .context("Pattern match case expression requires a union type")?;

                let mut explicit_cases = Vec::new();
                for explicit_case in explicit_cases_ast {
                    let explicit_case: (VariableSymbol, _) = (
                        explicit_case.variable_name.clone().into(),
                        explicit_case
                            .variable_definition
                            .type_infer(stack, ctx)
                            .with_context(|| {
                                format!(
                                    "While inferring type for case handler of variant '{:?}'",
                                    explicit_case.variable_name
                                )
                            })?,
                    );
                    explicit_cases.push(explicit_case)
                }

                let default_case = match default_case {
                    Some(exp) => Some(
                        exp.type_infer(stack, ctx)
                            .context("While inferring type for default case handler")?,
                    ),
                    None => None,
                };

                let mut cases = Vec::new();
                for member in members.iter() {
                    let explicit_case = explicit_cases
                        .iter()
                        .find(|(symbol, _)| symbol == member.name())
                        .map(|(_, ty)| ty);

                    let case = if let (Some(member_type), Some(explicit_case)) =
                        (member.member_type(), explicit_case)
                    {
                        type_infer_function_call(
                            explicit_case.clone(),
                            member_type.clone(),
                            stack,
                            ctx,
                        )
                        .with_context(|| {
                            format!(
                                "While applying case handler to variant '{:?}'",
                                member.name()
                            )
                        })?
                    } else {
                        match explicit_case.or(default_case.as_ref()).cloned() {
                            Some(case) => case,
                            None => Err(TypeInferenceError::CaseNotCovered(member.name().clone()))
                                .with_context(|| {
                                    let covered_cases: Vec<_> = explicit_cases.iter().map(|(s, _)| s).collect();
                                    format!("Pattern match incomplete. Covered variants: {:?}, Has default: {}", 
                                        covered_cases, default_case.is_some())
                                })?,
                        }
                    };
                    cases.push(case);
                }

                join(&cases, ctx).context("While joining result types from all case branches")
            }
        }
    }
}

fn join<'a>(
    elements: impl IntoIterator<Item = &'a TypeUnderConstruction>,
    ctx: &mut ConstraintContext,
) -> Result<TypeUnderConstruction> {
    let var = ctx.fresh_var();
    for elm in elements {
        ctx.add_constraint(Constraint::Subtype(
            elm.clone(),
            TypeUnderConstruction::Var(var.clone()),
        ));
    }
    Ok(TypeUnderConstruction::Var(var))
}
