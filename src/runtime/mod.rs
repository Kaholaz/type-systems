use std::{
    cell::{OnceCell, RefCell},
    fmt::{Debug, Display},
    rc::Rc,
};

use indexmap::IndexMap;
use nonempty::NonEmpty;

use crate::{
    ast::{
        self, Declaration, Expression, ExpressionValue, FileName, Program,
        StructFieldTypeDeclaration, TypeName, Value, VariableDeclaration, VariableName,
    },
    util::LinkedList,
};

#[derive(Debug, Clone)]
pub enum RuntimeValue {
    UnionValue {
        union_name: TypeName,
        union_value: UnionValue,
    },
    Struct {
        struct_name: TypeName,
        struct_fields: Vec<StructField>,
    },
    Tuple(Vec<Rc<RuntimeValue>>),
    Function {
        bind_variable: VariableName,
        expression: ExpressionValue,
        captured_stack: Stack,
    },
}

impl Display for RuntimeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeValue::UnionValue {
                union_name,
                union_value,
            } if union_name.as_str() == "Int" => {
                let UnionValue::UnionValue { member_name, value } = union_value else {
                    panic!("Illegal int value.")
                };
                if member_name.as_str() == "pos" {
                    let mut num = 0_isize;
                    let mut cur = value.as_ref();
                    while let RuntimeValue::UnionValue {
                        union_name: _,
                        union_value:
                            UnionValue::UnionValue {
                                member_name: _,
                                value,
                            },
                    } = cur
                    {
                        num += 1;
                        cur = value.as_ref();
                    }
                    write!(f, "{}", num)
                } else {
                    let mut num = -1_isize;
                    let mut cur = value.as_ref();
                    while let RuntimeValue::UnionValue {
                        union_name: _,
                        union_value:
                            UnionValue::UnionValue {
                                member_name: _,
                                value,
                            },
                    } = cur
                    {
                        num -= 1;
                        cur = value.as_ref();
                    }
                    write!(f, "{}", num)
                }
            }
            RuntimeValue::UnionValue {
                union_name,
                union_value,
            } => match union_value {
                UnionValue::SingularUnionValue { member_name } => {
                    write!(f, "{}[{}]", union_name, member_name)
                }
                UnionValue::UnionValue { member_name, value } => {
                    write!(f, "{}[{}={}]", union_name, member_name, value)
                }
            },
            RuntimeValue::Struct {
                struct_name,
                struct_fields,
            } => write!(
                f,
                "{}{{{}}}",
                struct_name,
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
                captured_stack: _,
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
        value: Rc<RuntimeValue>,
    },
}

#[derive(Debug, Clone)]
pub struct StructField {
    field_name: VariableName,
    value: Rc<RuntimeValue>,
}

#[derive(Debug)]
pub struct LazyRuntimeValue {
    lazy_value: Option<(Expression, Stack)>,
    value: OnceCell<Rc<RuntimeValue>>,
}

impl LazyRuntimeValue {
    fn lazy(expression: &Expression, stack: Stack) -> Self {
        Self {
            lazy_value: Some((expression.clone(), stack.clone())),
            value: OnceCell::new(),
        }
    }

    fn immediate(runtime_value: Rc<RuntimeValue>) -> Self {
        let out = Self {
            lazy_value: None,
            value: OnceCell::new(),
        };
        let _ = out.value.set(runtime_value);
        out
    }

    fn get(&self) -> Rc<RuntimeValue> {
        self.value
            .get_or_init(|| {
                let (expression, env) = self
                    .lazy_value
                    .as_ref()
                    .expect("Dereferenced illegaly constructed lazy runtime value!");
                expression.evaluate(env)
            })
            .clone()
    }
}

type Frame = IndexMap<VariableName, Rc<LazyRuntimeValue>>;
type Stack = LinkedList<Rc<RefCell<Frame>>>;

fn lookup(stack: &Stack, variable: &VariableName) -> Rc<RuntimeValue> {
    if let Some(int) = get_int_literal(variable) {
        return Rc::new(int);
    }

    stack
        .iter()
        .find_map(|f| f.borrow().get(variable).cloned())
        .expect("Could not lookup variable. This indicates an issue with the type checker.")
        .get()
}

fn get_int_literal(variable_name: &VariableName) -> Option<RuntimeValue> {
    if let Ok(int) = variable_name.as_str().parse::<isize>() {
        if int >= 0 {
            Some(RuntimeValue::UnionValue {
                union_name: TypeName::new("Int"),
                union_value: UnionValue::UnionValue {
                    member_name: VariableName::new("pos"),
                    value: Rc::new(do_get_int_literal(int)),
                },
            })
        } else {
            Some(RuntimeValue::UnionValue {
                union_name: TypeName::new("Int"),
                union_value: UnionValue::UnionValue {
                    member_name: VariableName::new("neg"),
                    value: Rc::new(do_get_int_literal(int)),
                },
            })
        }
    } else {
        None
    }
}

fn do_get_int_literal(int: isize) -> RuntimeValue {
    if int == 0 {
        RuntimeValue::UnionValue {
            union_name: TypeName::new("PosInt"),
            union_value: UnionValue::SingularUnionValue {
                member_name: VariableName::new("0"),
            },
        }
    } else if int >= 0 {
        RuntimeValue::UnionValue {
            union_name: TypeName::new("PosInt"),
            union_value: UnionValue::UnionValue {
                member_name: VariableName::new("pre"),
                value: Rc::new(do_get_int_literal(int - 1)),
            },
        }
    } else if int == -1 {
        RuntimeValue::UnionValue {
            union_name: TypeName::new("NegInt"),
            union_value: UnionValue::SingularUnionValue {
                member_name: VariableName::new("-1"),
            },
        }
    } else {
        RuntimeValue::UnionValue {
            union_name: TypeName::new("NegInt"),
            union_value: UnionValue::UnionValue {
                member_name: VariableName::new("pre"),
                value: Rc::new(do_get_int_literal(int + 1)),
            },
        }
    }
}

pub fn run_program(program: &Program) -> Vec<(VariableName, RuntimeValue)> {
    let stack = run_program_impl(program, &mut Vec::new());
    let (out, _) = stack.pop();
    out.take()
        .into_iter()
        .map(|(name, value)| (name, value.get().as_ref().clone()))
        .collect()
}

fn run_program_impl(program: &Program, already_imported: &mut Vec<FileName>) -> Stack {
    let mut import_statements = Vec::new();
    let mut statements = Vec::new();

    for definitions in &program.definitions {
        match definitions {
            Declaration::IncludeDeclaration(file_name, imported_program)
                if !already_imported.contains(file_name) =>
            {
                import_statements.push((file_name, &**imported_program));
            }
            Declaration::VariableDeclaration(variable_declaration) => {
                statements.push(variable_declaration);
            }
            _ => (), // discard type statements an duplicate imports
        }
    }

    let mut stack = None;
    for (file_name, imported_program) in import_statements {
        already_imported.push(file_name.clone());
        let imported_stack = run_program_impl(imported_program, already_imported);
        stack = match stack {
            None => Some(imported_stack),
            Some(stack) => Some(imported_stack.push_back(stack)),
        }
    }

    let stack = match stack {
        None => Stack::singleton(Rc::default()),
        Some(stack) => Stack::new(Rc::default(), stack),
    };
    let mut global_frame = stack.peek().0.borrow_mut();
    for VariableDeclaration {
        variable_name,
        variable_definition,
    } in statements
    {
        global_frame.insert(
            variable_name.clone(),
            Rc::new(LazyRuntimeValue::lazy(variable_definition, stack.clone())),
        );
    }
    drop(global_frame);

    stack
}

trait Evaluate: Debug {
    fn evaluate(&self, stack: &Stack) -> Rc<RuntimeValue>;
}

fn call_function(function: Rc<RuntimeValue>, arg: Rc<LazyRuntimeValue>) -> Rc<RuntimeValue> {
    match &*function {
        RuntimeValue::Function {
            bind_variable,
            expression,
            captured_stack,
        } => {
            let frame: Rc<RefCell<Frame>> = Rc::default();
            frame.borrow_mut().insert(bind_variable.clone(), arg);

            let stack = Stack::new(frame, captured_stack.clone());
            expression.evaluate(&stack)
        }
        _ => {
            panic!("Non-function called as a function! This indicates a bug with the type checker.")
        }
    }
}

impl Evaluate for Expression {
    fn evaluate(&self, stack: &Stack) -> Rc<RuntimeValue> {
        let (mut head, mut tail) = self.values.peek();
        let mut out = head.evaluate(stack);
        while let Some(args) = tail {
            (head, tail) = args.peek();
            out = call_function(
                out,
                Rc::new(LazyRuntimeValue::immediate(head.evaluate(stack))),
            )
        }
        out
    }
}

impl Evaluate for ExpressionValue {
    fn evaluate(&self, stack: &Stack) -> Rc<RuntimeValue> {
        match self {
            ExpressionValue::FunctionDeclaration(assignment, expression) => {
                let StructFieldTypeDeclaration {
                    field_name: variable_name,
                    type_expression: _,
                } = assignment;
                Rc::new(RuntimeValue::Function {
                    bind_variable: variable_name.clone(),
                    expression: expression.as_ref().clone(),
                    captured_stack: stack.clone(),
                })
            }
            ExpressionValue::ValueExpression(value) => value.evaluate(stack),
            ExpressionValue::TypeExpression(type_name, spec) => match spec {
                crate::ast::Spec::UnionValue(union_value) => {
                    evaluate_union_value(type_name.clone(), union_value, stack)
                }
                crate::ast::Spec::StructValue(fields) => {
                    evaluate_fields(type_name.clone(), fields, stack)
                }
            },
        }
    }
}

impl Evaluate for Value {
    fn evaluate(&self, stack: &Stack) -> Rc<RuntimeValue> {
        match self {
            Value::Variable(variable) => lookup(stack, variable),
            Value::Expression(expression) => expression.evaluate(stack),
            Value::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|e| e.evaluate(stack))
                    .collect::<Vec<_>>();
                Rc::new(RuntimeValue::Tuple(elements))
            }
            Value::StructAccess(value, field_name) => match &*value.evaluate(stack) {
                RuntimeValue::Struct {
                    struct_name: _,
                    struct_fields: fields,
                } => match fields.iter().find(|f| &f.field_name == field_name) {
                    Some(field) => field.value.clone(),
                    None => panic!(
                        "Tried to access a field that does not exist. This indicates an error in the type checker."
                    ),
                },
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
) -> Rc<RuntimeValue> {
    let value = value.evaluate(stack);
    match &*value {
        RuntimeValue::UnionValue {
            union_name: _,
            union_value: UnionValue::SingularUnionValue { member_name },
        } => {
            let expression = explicit_cases
                .iter()
                .find_map(|f| {
                    if &f.variable_name == member_name {
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
        RuntimeValue::UnionValue {
            union_name: _,
            union_value:
                UnionValue::UnionValue {
                    member_name,
                    value: member_value,
                },
        } => {
            let explicit_case = explicit_cases.iter().find_map(
                |VariableDeclaration {
                     variable_name,
                     variable_definition,
                 }| {
                    if variable_name == member_name {
                        Some(variable_definition)
                    } else {
                        None
                    }
                },
            );
            match explicit_case {
                Some(function) => {
                    call_function(function.evaluate(stack), Rc::new(LazyRuntimeValue::immediate(member_value.clone())))
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

fn evaluate_union_value(
    union_name: TypeName,
    union_value: &ast::UnionValue,
    stack: &Stack,
) -> Rc<RuntimeValue> {
    match union_value {
        ast::UnionValue::VariableDeclaration(variable_declaration) => {
            let value = variable_declaration.variable_definition.evaluate(stack);
            Rc::new(RuntimeValue::UnionValue {
                union_name,
                union_value: UnionValue::UnionValue {
                    member_name: variable_declaration.variable_name.clone(),
                    value,
                },
            })
        }
        ast::UnionValue::VariableName(variable_name) => Rc::new(RuntimeValue::UnionValue {
            union_name,
            union_value: UnionValue::SingularUnionValue {
                member_name: variable_name.clone(),
            },
        }),
    }
}

fn evaluate_fields(
    struct_name: TypeName,
    struct_fieds: &[VariableDeclaration],
    stack: &Stack,
) -> Rc<RuntimeValue> {
    let struct_fields = struct_fieds
        .iter()
        .map(|f| {
            let value = f.variable_definition.evaluate(stack);
            StructField {
                field_name: f.variable_name.clone(),
                value,
            }
        })
        .collect::<Vec<_>>();
    Rc::new(RuntimeValue::Struct {
        struct_name,
        struct_fields,
    })
}
