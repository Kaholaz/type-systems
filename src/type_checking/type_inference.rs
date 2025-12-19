use crate::{
    ast::{
        Declaration, EnumElementTypeDeclaration, Expression, ExpressionValue, NominalType, Program,
        Spec, StructFieldTypeDeclaration, TypeDeclaration, TypeDefinition, TypeExpression,
        TypeValue, UnionValue, Value, VariableDeclaration,
    },
    type_checking::{
        Constraint, ConstraintContext, StructField, SymbolOrPlaceholder, TypeMapSymbol, TypeSymbol,
        TypeUnderConstruction, UnionMember, VariableSymbol, is_pure_type,
    },
    util::LinkedList,
};
use anyhow::{Context, Result, bail};
use std::{collections::HashMap, fmt::Display};
use thiserror::Error;

#[derive(Error, Debug, Clone)]
pub enum TypeInferenceError {
    #[error("Unknown variable '{0}' - variable not found in current scope or any parent scope")]
    UnknownVariable(VariableSymbol),

    #[error("Unknown type '{0}' - type not declared or not in scope")]
    UnknownType(TypeSymbol),

    #[error("Duplicate variable definition '{0}' - variable already defined in this scope")]
    DuplicateVariableDefinition(VariableSymbol),

    #[error("Duplicate type definition '{0}' - type already defined in this scope")]
    DuplicateTypeDefinition(TypeSymbol),

    #[error(
        "Illegal function arity - attempted to call a non-function value or provided wrong number of arguments"
    )]
    IllegalArity,

    #[error("Struct field '{0}' does not exist on this struct type")]
    StructFieldDoesNotExist(VariableSymbol),

    #[error(
        "Attempted to access field on a non-struct type - only struct types support field access"
    )]
    StructAccessOfNonStruct,

    #[error(
        "Not all required struct fields were specified - missing one or more field initializers"
    )]
    NotAllStructFieldsSpecified,

    #[error("Union variant '{0}' does not exist on this union type")]
    VariantDoesNotExist(VariableSymbol),

    #[error("Cannot construct type - type definition and initializer structure are incompatible")]
    CannotConstruct,

    #[error("Pattern match (case) expression must be performed on a Union type, not other types")]
    CasesOfNonUnionType,

    #[error("Pattern match incomplete - variant '{0}' is not handled and no default case provided")]
    CaseNotCovered(VariableSymbol),

    #[error("Branches produces different types: {0}")]
    UnificationError(DisplayTypes),
}

#[derive(Debug, Clone)]
pub struct DisplayTypes(Vec<TypeUnderConstruction>);
impl Display for DisplayTypes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|t| format!("'{}'", t))
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
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
                .with_context(|| format!("While searching parent scopes for symbol {}", symbol)),
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
                    format!("While registering variable declaration '{}'", variable_name)
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
                    .with_context(|| format!("Type '{}' is illegaly defined", type_name))?
                {
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
                    .with_context(|| format!("Could not infer type of '{}'", variable_name))?;

                ctx.add_constraint(Constraint::Equal(var_type.clone(), inferred_type.clone()))?;

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
            TypeDefinition::NominalType(nominal_type) => nominal_type.type_infer(stack, ctx),
            TypeDefinition::TypeExpression(tyexpression) => tyexpression.type_infer(stack, ctx),
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
                            format!("Struct field '{}' illegaly defined", field_name)
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
                                format!("Union variant '{}' illegaly defined", element_name)
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
            TypeExpression::TypeValue(type_value) => type_value.type_infer(stack, ctx),
            TypeExpression::FunctionType(arguments) => {
                let arguments = type_infer_arguments(arguments, stack, ctx)?;
                Ok(TypeUnderConstruction::Function(arguments))
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
    let arg = arg.type_infer(stack, ctx)?;
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
            TypeValue::TypeName(tyname) => lookup_symbol(stack, &(tyname.clone().into())).cloned(),
            TypeValue::TypeTuple(tuple_members) => {
                let tuple_members = tuple_members
                    .iter()
                    .map(|m| m.type_infer(stack, ctx))
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
        let mut value = function.type_infer(stack, ctx)?;

        for (i, arg) in args.iter().flat_map(|args| args.iter()).enumerate() {
            let arg = arg.type_infer(stack, ctx).with_context(|| {
                format!(
                    "Cannot infer type of argument at index {} in function call",
                    i
                )
            })?;
            value = type_infer_function_call(value, arg, stack, ctx)?
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

            let args = LinkedList::singleton(TypeUnderConstruction::Var(ret_var.clone()));
            let args = args.push(TypeUnderConstruction::Var(arg_var.clone()));
            ctx.add_constraint(Constraint::Equal(
                function,
                TypeUnderConstruction::Function(Box::new(args)),
            ))?;
            Ok(TypeUnderConstruction::Var(ret_var))
        }
        TypeUnderConstruction::Function(args) => {
            let (arg, args) = args.pop();
            ctx.add_constraint(Constraint::Subtype(argument, arg))?;

            let args = args.expect("Functions always have a return type");
            if args.len() > 1 {
                Ok(TypeUnderConstruction::Function(args))
            } else {
                Ok(args.pop().0)
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
                let argument_type = argument_type.type_infer(stack, ctx)?;
                frame.insert(argument_name.clone().into(), argument_type.clone());

                let stack = &TypeStack {
                    frame,
                    prev: Some(stack),
                };

                let return_type = function_body.type_infer(stack, ctx)?;

                let out = match return_type {
                    TypeUnderConstruction::Function(args) => {
                        TypeUnderConstruction::Function(LinkedList::cons(argument_type, args))
                    }
                    _ => TypeUnderConstruction::Function(Box::new(
                        LinkedList::singleton(return_type).push(argument_type),
                    )),
                };
                Ok(out)
            }
            ExpressionValue::ValueExpression(value) => value.type_infer(stack, ctx),
            ExpressionValue::TypeExpression(tyname, spec) => {
                let ty = lookup_symbol(stack, &tyname.clone().into())?;

                match (ty, spec) {
                    (
                        TypeUnderConstruction::Struct(struct_name, type_fields),
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
                                    .with_context(|| format!("While inferring type for struct field '{}' in struct constructor", variable_name))?,
                            };
                            spec.push(field)
                        }

                        let mut all_fields_are_present = true;
                        for StructField { name, field_type } in type_fields {
                            let spec_type = spec.iter().find(|sf| &sf.name == name);
                            if let Some(spec_type) = spec_type {
                                ctx.add_constraint(Constraint::Subtype(
                                    spec_type.field_type.clone(),
                                    field_type.clone(),
                                ))?;
                            } else {
                                all_fields_are_present = false
                            }
                        }

                        if all_fields_are_present {
                            Ok(ty.clone())
                        } else {
                            Err(TypeInferenceError::NotAllStructFieldsSpecified).with_context(
                                || format!("While constructing struct type '{}'", struct_name),
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
                                            "Cannot create union variant '{}' of union '{}'",
                                            variable_name, union_name
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
                                .with_context(|| format!("Cannot construct union of '{}'", union_name))?,
                            Some(union_member) => match (union_member.member_type(), spec_type) {
                                (None, None) => Ok(ty.clone()),
                                (Some(union_member_type), Some(spec_type)) => {
                                    ctx.add_constraint(Constraint::Subtype(
                                        spec_type,
                                        union_member_type.clone(),
                                    ))?;
                                    Ok(ty.clone())
                                }
                                (_, _) => Err(TypeInferenceError::CannotConstruct)
                                    .with_context(|| format!("Mismatch between union variant '{}' definition and provided value", spec_name))?,
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
            Value::Variable(variable_name) => {
                lookup_symbol(stack, &variable_name.clone().into()).cloned()
            }
            Value::Expression(expression) => expression.type_infer(stack, ctx),
            Value::Tuple(elements) => elements
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    e.type_infer(stack, ctx).with_context(|| {
                        format!("Cannot infer type of tuple element at index {}", i)
                    })
                })
                .collect::<Result<Vec<_>, _>>()
                .map(TypeUnderConstruction::Tuple),
            Value::StructAccess(value, variable_name) => {
                let value = value
                    .type_infer(stack, ctx)
                    .context("Failed to infer type of struct before struct access")?;

                let fields = match value {
                    TypeUnderConstruction::Struct(_, fields) => fields,
                    TypeUnderConstruction::RecurseMarker(s) => {
                        match lookup_symbol(stack, &s.into())? {
                            TypeUnderConstruction::Struct(_, fields) => fields.clone(),
                            _ => bail!(TypeInferenceError::StructAccessOfNonStruct),
                        }
                    }
                    _ => bail!(TypeInferenceError::StructAccessOfNonStruct),
                };

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
                            "Available fields: {}",
                            fields
                                .iter()
                                .map(|f| format!("'{}'", f.name))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    })?,
                }
            }
            Value::Case(value, explicit_cases_ast, default_case) => {
                let value = value.type_infer(stack, ctx)?;

                let (union_name, members) = match value {
                    TypeUnderConstruction::Union(union_name, members) => (union_name, members),
                    TypeUnderConstruction::RecurseMarker(s) => {
                        match lookup_symbol(stack, &s.into())? {
                            TypeUnderConstruction::Union(union_name, members) => {
                                (union_name.clone(), members.clone())
                            }
                            _ => bail!(TypeInferenceError::CasesOfNonUnionType),
                        }
                    }
                    _ => bail!(TypeInferenceError::CasesOfNonUnionType),
                };

                let mut explicit_cases = Vec::new();
                for explicit_case in explicit_cases_ast {
                    let explicit_case: (VariableSymbol, _) = (
                        explicit_case.variable_name.clone().into(),
                        explicit_case.variable_definition.type_infer(stack, ctx)?,
                    );
                    explicit_cases.push(explicit_case)
                }

                let default_case = match default_case {
                    Some(exp) => {
                        let out = exp
                            .type_infer(stack, ctx)
                            .context("Could not infer type of default case")?;
                        Some(out)
                    }
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
                        )?
                    } else {
                        match explicit_case.or(default_case.as_ref()).cloned() {
                            Some(case) => case,
                            None => Err(TypeInferenceError::CaseNotCovered(member.name().clone()))
                                .with_context(|| {
                                    let covered_cases: Vec<_> = explicit_cases.iter().map(|(s, _)| s).collect();
                                    format!("Pattern match incomplete. Covered variants: {}, Has default: {}", 
                                        covered_cases.iter().map(|c| format!("'{}'", c)).collect::<Vec<_>>().join(", "), default_case.is_some())
                                })?,
                        }
                    };
                    cases.push(case);
                }

                join(&cases, ctx)
                    .context(format!("Could not unify cases for Union '{}'", union_name))
            }
        }
    }
}

fn join(
    elements: &Vec<TypeUnderConstruction>,
    ctx: &mut ConstraintContext,
) -> Result<TypeUnderConstruction> {
    if elements.iter().all(is_pure_type) {
        let mut elms = elements.iter();
        let first = elms.next().expect("cannot join zero types");
        let (equal, _) = elms.fold((true, first), |(equal, prev), curr| {
            (equal && prev == curr, curr)
        });
        if equal {
            return Ok(first.clone());
        } else {
            bail!(TypeInferenceError::UnificationError(DisplayTypes(
                elements.to_vec()
            )))
        }
    }

    let var = ctx.fresh_var();
    for elm in elements {
        ctx.add_constraint(Constraint::Subtype(
            elm.clone(),
            TypeUnderConstruction::Var(var.clone()),
        ))?;
    }
    Ok(TypeUnderConstruction::Var(var))
}
