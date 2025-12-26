use std::{
    cell::OnceCell,
    collections::HashMap,
    fmt::{Debug, Display},
};

use nonempty::NonEmpty;

use crate::{
    ast::{
        self, Expression, ExpressionValue, Program, StructFieldTypeDeclaration, Value,
        VariableDeclaration, VariableName,
    },
    util::LinkedList,
};

#[derive(Debug, Clone)]
pub enum RuntimeValue {
    UnionValue(UnionValue),
    Struct(Vec<StructField>),
    Tuple(Vec<RuntimeValue>),
    Function {
        bind_variable: VariableName,
        expression: ExpressionValue,
        captured_env: Frame,
    },
}

impl Display for RuntimeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeValue::UnionValue(union_value) => match union_value {
                UnionValue::SingularUnionValue { member_name } => write!(f, "[{}]", member_name),
                UnionValue::UnionValue { member_name, value } => {
                    write!(f, "[{}={}]", member_name, value)
                }
            },
            RuntimeValue::Struct(struct_fields) => write!(
                f,
                "{{{}}}",
                struct_fields
                    .iter()
                    .map(|f| format!("{}={}", f.field_name, f.value))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            RuntimeValue::Tuple(elements) => write!(
                f,
                "({})",
                elements
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            RuntimeValue::Function {
                bind_variable: _,
                expression: _,
                captured_env: _,
            } => write!(f, "function"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnionValue {
    SingularUnionValue {
        member_name: VariableName,
    },
    UnionValue {
        member_name: VariableName,
        value: Box<RuntimeValue>,
    },
}

#[derive(Debug, Clone)]
pub struct StructField {
    field_name: VariableName,
    value: Box<RuntimeValue>,
}

#[derive(Debug, Clone)]
pub struct LazyRuntimeValue {
    lazy_value: Option<Expression>,
    value: OnceCell<RuntimeValue>,
}

impl LazyRuntimeValue {
    fn lazy(expression: &Expression) -> Self {
        Self {
            lazy_value: Some(expression.clone()),
            value: OnceCell::new(),
        }
    }

    fn immediate_expr(expression: &Expression, stack: &Stack) -> Self {
        let out = Self {
            lazy_value: None,
            value: OnceCell::new(),
        };
        let _ = out.value.set(expression.evaluate(stack));
        out
    }

    fn immediate_expr_value(expression_value: &ExpressionValue, stack: &Stack) -> Self {
        let out = Self {
            lazy_value: None,
            value: OnceCell::new(),
        };
        let _ = out.value.set(expression_value.evaluate(stack));
        out
    }

    fn immediate_runtime_value(runtime_value: RuntimeValue) -> Self {
        let out = Self {
            lazy_value: None,
            value: OnceCell::new(),
        };
        let _ = out.value.set(runtime_value);
        out
    }

    fn get_runtime_value(&self, stack: &Stack) -> &RuntimeValue {
        self.value.get_or_init(|| {
            self.lazy_value
                .as_ref()
                .expect("Dereferenced illegaly constructed lazy runtime value!")
                .evaluate(stack)
        })
    }

    fn take(mut self, stack: &Stack) -> RuntimeValue {
        self.value.take().unwrap_or_else(|| {
            self.lazy_value
                .expect("Illegaly constructed lazy runtime value!")
                .evaluate(stack)
        })
    }
}

type Frame = HashMap<VariableName, LazyRuntimeValue>;
type Stack<'a> = LinkedList<&'a Frame>;

fn lookup<'a>(stack: &'a Stack, variable: &VariableName) -> &'a RuntimeValue {
    fn strip_stack<'a>(
        stack: &'a Stack,
        variable: &VariableName,
    ) -> (&'a LazyRuntimeValue, &'a Stack<'a>) {
        let (head, tail) = stack.peek();
        if let Some(value) = head.get(variable) {
            return (value, stack);
        }

        match tail {
            Some(stack) => strip_stack(stack, variable),
            None => panic!(
                "Variable '{}' not found. This indicates a bug in the type checker (or the runtime).",
                variable
            ),
        }
    }

    let (value, stack) = strip_stack(stack, variable);
    value.get_runtime_value(stack)
}

pub fn run_program(program: &Program) -> Vec<(VariableName, RuntimeValue)> {
    let mut global = Frame::new();

    // first pass: collect everything
    for definitions in &program.definitions {
        match definitions {
            ast::Declaration::IncludeDeclaration(_file_name) => todo!("not implemented yet"),
            ast::Declaration::TypeDeclaration(_) => (),
            ast::Declaration::VariableDeclaration(variable_declaration) => {
                let VariableDeclaration {
                    variable_name,
                    variable_definition,
                } = variable_declaration;
                global.insert(
                    variable_name.clone(),
                    LazyRuntimeValue::lazy(variable_definition),
                );
            }
        }
    }

    // second pass: actually evaluate
    let stack = Stack::singleton(&global);
    let mut result = Vec::new();
    for definitions in &program.definitions {
        match definitions {
            ast::Declaration::IncludeDeclaration(_file_name) => todo!("not implemented yet"),
            ast::Declaration::TypeDeclaration(_) => (),
            ast::Declaration::VariableDeclaration(variable_declaration) => {
                let VariableDeclaration {
                    variable_name,
                    variable_definition,
                } = variable_declaration;
                result.push((variable_name.clone(), variable_definition.evaluate(&stack)));
            }
        }
    }

    result
}

trait Evaluate: Debug {
    fn evaluate(&self, stack: &Stack) -> RuntimeValue;
}

fn call_function(function: &RuntimeValue, arg: LazyRuntimeValue) -> RuntimeValue {
    match function {
        RuntimeValue::Function {
            bind_variable,
            expression,
            captured_env,
        } => {
            let mut frame = Frame::new();
            frame.insert(bind_variable.clone(), arg);

            let captured_stack = Stack::singleton(captured_env);
            let stack = Stack::unpeek(&frame, &captured_stack);
            expression.evaluate(&stack)
        }
        _ => {
            panic!("Non-function called as a function! This indicates a bug with the type checker.")
        }
    }
}

impl Evaluate for Expression {
    fn evaluate(&self, stack: &Stack) -> RuntimeValue {
        let (mut head, mut tail) = self.values.peek();
        let mut out = head.evaluate(stack);
        while let Some(args) = tail {
            (head, tail) = args.peek();
            out = call_function(&out, LazyRuntimeValue::immediate_expr_value(head, stack))
        }
        out
    }
}

fn capture_environment(stack: &Stack) -> Frame {
    let mut captured = Frame::new();
    for frame in stack {
        for (name, value) in *frame {
            if !captured.contains_key(name) {
                captured.insert(name.clone(), value.clone());
            }
        }
    }

    captured
}

impl Evaluate for ExpressionValue {
    fn evaluate(&self, stack: &Stack) -> RuntimeValue {
        match self {
            ExpressionValue::FunctionDeclaration(assignment, expression) => {
                let StructFieldTypeDeclaration {
                    field_name: variable_name,
                    type_expression: _,
                } = assignment;
                RuntimeValue::Function {
                    bind_variable: variable_name.clone(),
                    expression: expression.as_ref().clone(),
                    captured_env: capture_environment(stack),
                }
            }
            ExpressionValue::ValueExpression(value) => value.evaluate(stack),
            ExpressionValue::TypeExpression(_, spec) => match spec {
                crate::ast::Spec::UnionValue(union_value) => union_value.evaluate(stack),
                crate::ast::Spec::StructValue(fields) => fields.evaluate(stack),
            },
        }
    }
}

impl Evaluate for Value {
    fn evaluate(&self, stack: &Stack) -> RuntimeValue {
        match self {
            Value::Variable(variable) => {
                let value = lookup(stack, variable);
                value.clone()
            }
            Value::Expression(expression) => expression.evaluate(stack),
            Value::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|e| e.evaluate(stack))
                    .collect::<Vec<_>>();
                RuntimeValue::Tuple(elements)
            }
            Value::StructAccess(value, field_name) => match value.evaluate(stack) {
                RuntimeValue::Struct(fields) => {
                    match fields.into_iter().find(|f| &f.field_name == field_name) {
                        Some(field) => *field.value,
                        None => panic!(
                            "Tried to access a field that does not exist. This indicates an error in the type checker."
                        ),
                    }
                }
                _ => panic!(
                    "Tried to acces the field of a non-struct. This indicates an error in the type checker."
                ),
            },
            Value::Case(value, explicit_cases, default_case) => {
                evaluate_case(stack, value, explicit_cases, default_case.as_ref())
            }
        }
    }
}

fn evaluate_case(
    stack: &Stack,
    value: &Value,
    explicit_cases: &NonEmpty<VariableDeclaration>,
    default_case: Option<&Expression>,
) -> RuntimeValue {
    let value = value.evaluate(stack);
    match value {
        RuntimeValue::UnionValue(UnionValue::SingularUnionValue { member_name }) => {
            let expression = explicit_cases
                .iter()
                .find_map(|f| {
                    if f.variable_name == member_name {
                        Some(&f.variable_definition)
                    } else {
                        None
                    }
                })
                .or(default_case)
                .expect(
                    "No case found for union value. This indicates an error in the type checker.",
                );
            expression.evaluate(stack)
        }
        RuntimeValue::UnionValue(UnionValue::UnionValue {
            member_name,
            value: member_value,
        }) => {
            let explicit_case = explicit_cases.iter().find_map(
                |VariableDeclaration {
                     variable_name,
                     variable_definition,
                 }| {
                    if variable_name == &member_name {
                        Some(variable_definition)
                    } else {
                        None
                    }
                },
            );
            match explicit_case {
                Some(function) => {
                    call_function(&function.evaluate(stack), LazyRuntimeValue::immediate_runtime_value(*member_value))
                }
                None => default_case.expect(
                    "No case found for union value. This indicates an error in the type checker.",
                ).evaluate(stack),
            }
        }
        _ => panic!(
            "Non union value provided for case evaluation. This indicates an error in the type checker."
        ),
    }
}

impl Evaluate for ast::UnionValue {
    fn evaluate(&self, stack: &Stack) -> RuntimeValue {
        match self {
            ast::UnionValue::VariableDeclaration(variable_declaration) => {
                let value = variable_declaration.variable_definition.evaluate(stack);
                RuntimeValue::UnionValue(UnionValue::UnionValue {
                    member_name: variable_declaration.variable_name.clone(),
                    value: Box::new(value),
                })
            }
            ast::UnionValue::VariableName(variable_name) => {
                RuntimeValue::UnionValue(UnionValue::SingularUnionValue {
                    member_name: variable_name.clone(),
                })
            }
        }
    }
}

impl Evaluate for Vec<VariableDeclaration> {
    fn evaluate(&self, stack: &Stack) -> RuntimeValue {
        let fields = self
            .iter()
            .map(|f| {
                let value = f.variable_definition.evaluate(stack);
                StructField {
                    field_name: f.variable_name.clone(),
                    value: Box::new(value),
                }
            })
            .collect::<Vec<_>>();
        RuntimeValue::Struct(fields)
    }
}
