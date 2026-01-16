use std::{fmt::format, fs::read_to_string};

use crate::{
    ast::{
        Declaration, EnumElementTypeDeclaration, Expression, ExpressionValue, FileName,
        NominalType, Program, Spec, StructFieldTypeDeclaration, TypeDeclaration, TypeDefinition,
        TypeExpression, TypeName, TypeValue, UnionValue, Value, VariableDeclaration, VariableName,
    },
    parser::{ParserError, TERMINATING_CHARACTERS, scanner::Scanner},
    util::LinkedList,
};
use anyhow::{Context, Result, bail};
use nonempty::NonEmpty;

pub trait Parsable
where
    Self: Sized,
{
    fn parse(scanner: &mut Scanner) -> Result<Self>;
}

// *******************
// * Top level nodes *
// *******************
/// program is definition sequence
/// <prog> ::= <def> {',' <def>}
impl Parsable for Program {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let head =
            Declaration::parse(scanner).context("failed to parse first declaration in program")?;
        let mut tail = Vec::new();
        while !scanner.is_at_end() {
            scanner
                .expect_character(',', "expected `,` between definitions".to_string())
                .context("invalid separator between declarations")?;
            scanner.skip_whitespace();
            if scanner.is_at_end() {
                break;
            }
            let definition = Declaration::parse(scanner).with_context(|| {
                format!("failed to parse declaration at position {}", tail.len() + 1)
            })?;
            tail.push(definition);
        }
        let definitions = nonempty::NonEmpty { head, tail };
        Ok(Program { definitions })
    }
}

/// <def> ::= '@' <file_name> | <tdef> | <vdef>
impl Parsable for Declaration {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        scanner.skip_whitespace();
        if scanner.is_at_end() {
            bail!(ParserError {
                message: "unexpected EOF when parsing declarations".to_string(),
                span: scanner.line_and_column(),
            });
        }

        let c = *scanner
            .current_char()
            .context("failed to read current character")?;

        if c == '@' {
            scanner
                .advance_and_skip_whitespace()
                .context("failed to advance after '@'")?;
            let filename =
                FileName::parse(scanner).context("failed to parse include declaration filename")?;
            let include_source = read_to_string(filename.as_str())
                .with_context(|| format!("while importing {}", filename.clone()))?;
            let included_program = crate::parser::parse(include_source)?;
            Ok(Declaration::IncludeDeclaration(
                filename,
                Box::new(included_program),
            ))
        } else if c.is_uppercase() {
            TypeDeclaration::parse(scanner)
                .map(Self::TypeDeclaration)
                .context("failed to parse type declaration")
        } else {
            VariableDeclaration::parse(scanner)
                .map(Self::VariableDeclaration)
                .context("failed to parse variable declaration")
        }
    }
}

/// '@' <file_name>
impl Parsable for FileName {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let mut file_name = Vec::new();
        while !scanner.is_at_end()
            && !scanner.current_char()?.is_whitespace()
            && *scanner.current_char()? != ','
        {
            file_name.push(*scanner.current_char()?);
            scanner.advance()?;
        }
        if file_name.is_empty() {
            bail!(ParserError {
                message: "expected filename".to_string(),
                span: scanner.line_and_column(),
            });
        }
        Ok(Self::new(file_name.into_iter().collect::<String>()))
    }
}

// *********
// * Types *
// *********
/// <tdef> ::= <tname> '=' ( <tnom> | <texp> ).
impl Parsable for TypeDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let type_name =
            TypeName::parse(scanner).context("failed to parse type name in type declaration")?;

        if *scanner.current_char()? != '=' {
            bail!(ParserError {
                message: "expected `=` in type declaration".to_string(),
                span: scanner.line_and_column(),
            });
        }
        scanner
            .advance_and_skip_whitespace()
            .context("failed to advance after '=' in type declaration")?;

        let type_definition = TypeDefinition::parse(scanner)
            .with_context(|| format!("failed to parse type definition for '{}'", type_name))?;

        Ok(Self {
            type_name,
            type_definition,
        })
    }
}

/// <tname>
impl Parsable for TypeName {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        if !scanner.current_char()?.is_uppercase() {
            bail!(ParserError {
                message: "type names must start with an uppercase letter".to_string(),
                span: scanner.line_and_column(),
            });
        }
        let type_name = scanner.get_chars_until_whitespace();
        Ok(TypeName::new(type_name))
    }
}

impl Parsable for TypeDefinition {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        match scanner.current_char()? {
            '[' | '{' => NominalType::parse(scanner)
                .map(Self::NominalType)
                .context("failed to parse nominal type"),
            _ => TypeExpression::parse(scanner)
                .map(Self::TypeExpression)
                .context("failed to parse type expression"),
        }
    }
}

/// <tnom> ::= '{' <decl> {',' <decl>} '}' | '\[' <elem> {',' <elem>} '\]'
impl Parsable for NominalType {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        match scanner.current_char()? {
            '{' => {
                scanner
                    .advance_and_skip_whitespace()
                    .context("failed to advance after '{' in struct type")?;

                let head = StructFieldTypeDeclaration::parse(scanner)
                    .context("failed to parse first struct field")?;
                let mut tail = Vec::new();

                while *scanner.current_char()? == ',' {
                    scanner
                        .advance_and_skip_whitespace()
                        .context("failed to advance after ',' in struct type")?;
                    tail.push(StructFieldTypeDeclaration::parse(scanner).with_context(|| {
                        format!(
                            "failed to parse struct field at position {}",
                            tail.len() + 1
                        )
                    })?)
                }

                scanner
                    .expect_character(
                        '}',
                        "expected `}` at the end of struct type declaration".to_string(),
                    )
                    .context("struct type not properly closed")?;
                scanner.skip_whitespace();
                Ok(Self::StructType(NonEmpty { head, tail }))
            }
            '[' => {
                scanner
                    .advance_and_skip_whitespace()
                    .context("failed to advance after '[' in enum type")?;

                let head = EnumElementTypeDeclaration::parse(scanner)
                    .context("failed to parse first enum element")?;
                let mut tail = Vec::new();

                while *scanner.current_char()? == ',' {
                    scanner
                        .advance_and_skip_whitespace()
                        .context("failed to advance after ',' in enum type")?;
                    tail.push(EnumElementTypeDeclaration::parse(scanner).with_context(|| {
                        format!(
                            "failed to parse enum element at position {}",
                            tail.len() + 1
                        )
                    })?)
                }

                scanner
                    .expect_character(
                        ']',
                        "expected `]` at the end of enum type declaration".to_string(),
                    )
                    .context("enum type not properly closed")?;
                scanner.skip_whitespace();
                Ok(Self::EnumType(NonEmpty { head, tail }))
            }
            _ => Err(ParserError {
                message: "unexpected character when parsing nominal type".to_string(),
                span: scanner.line_and_column(),
            }
            .into()),
        }
    }
}

/// <decl> ::= <vname> ':' <texp>
impl Parsable for StructFieldTypeDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let field_name = VariableName::parse(scanner).context("failed to parse field name")?;

        scanner
            .expect_character(
                ':',
                "expected `:` when parsing field type declaration".to_string(),
            )
            .with_context(|| format!("invalid field declaration for '{}'", field_name))?;
        scanner.skip_whitespace();

        let type_expression = TypeExpression::parse(scanner).with_context(|| {
            format!("failed to parse type expression for field '{}'", field_name)
        })?;

        Ok(Self {
            field_name,
            type_expression,
        })
    }
}

/// <elem> ::= <vname> [':' <texp>]
impl Parsable for EnumElementTypeDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let element_name =
            VariableName::parse(scanner).context("failed to parse enum element name")?;

        let type_expression = if *scanner.current_char()? == ':' {
            scanner
                .advance_and_skip_whitespace()
                .context("failed to advance after ':' in enum element")?;
            Some(TypeExpression::parse(scanner).with_context(|| {
                format!("failed to parse type for enum element '{}'", element_name)
            })?)
        } else {
            None
        };

        Ok(Self {
            element_name,
            type_expression,
        })
    }
}

/// <texp> ::= <tval> | <tval> '->' <texp>
impl Parsable for TypeExpression {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let type_value = TypeValue::parse(scanner).context("failed to parse type value")?;

        if !scanner.is_at_end()
            && !TERMINATING_CHARACTERS.contains(scanner.current_char()?)
            && *scanner.current_char()? == '-'
        {
            scanner.advance()?;
            scanner
                .expect_character('>', "expected `>` in arrow of type expression".to_string())
                .context("invalid function type arrow '->' syntax")?;
            scanner.skip_whitespace();

            let arg = type_value;
            match TypeExpression::parse(scanner)
                .context("failed to parse result type in function type")?
            {
                TypeExpression::TypeValue(result) => {
                    Ok(Self::FunctionType(Box::new(LinkedList::singleton(*result))))
                }
                TypeExpression::FunctionType(args) => {
                    Ok(Self::FunctionType(LinkedList::cons(arg, args)))
                }
            }
        } else {
            Ok(Self::TypeValue(Box::new(type_value)))
        }
    }
}

/// <tval> ::= <tname> | '(' <texp> {',' <texp>} ')'
impl Parsable for TypeValue {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        if *scanner.current_char()? == '(' {
            scanner
                .advance_and_skip_whitespace()
                .context("failed to advance after '(' in type tuple")?;

            let head = TypeExpression::parse(scanner)
                .context("failed to parse first type in type tuple")?;
            let mut tail = Vec::new();

            while *scanner.current_char()? == ',' {
                scanner
                    .advance_and_skip_whitespace()
                    .context("failed to advance after ',' in type tuple")?;
                tail.push(TypeExpression::parse(scanner).with_context(|| {
                    format!(
                        "failed to parse type at position {} in type tuple",
                        tail.len() + 1
                    )
                })?);
            }

            scanner
                .expect_character(
                    ')',
                    "expected `)` after parenthesized type expression".to_string(),
                )
                .context("type tuple not properly closed")?;
            scanner.skip_whitespace();
            Ok(Self::TypeTuple(NonEmpty { head, tail }))
        } else {
            TypeName::parse(scanner)
                .map(Self::TypeName)
                .context("failed to parse type name")
        }
    }
}

// **********
// * Values *
// **********
/// <vdef> ::= <vname> '=' <vexp>
impl Parsable for VariableDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let variable_name =
            VariableName::parse(scanner).context("failed to parse variable name")?;

        scanner
            .expect_character('=', "expected `=` in variable declaration".to_string())
            .with_context(|| format!("invalid variable declaration for '{}'", variable_name))?;
        scanner.skip_whitespace();

        let variable_definition = Expression::parse(scanner).with_context(|| {
            format!(
                "failed to parse expression for variable '{}'",
                variable_name
            )
        })?;

        Ok(Self {
            variable_name,
            variable_definition,
        })
    }
}

/// <vname>
impl Parsable for VariableName {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let variable_name = scanner.get_chars_until_whitespace();
        if variable_name.is_empty() {
            bail!(ParserError {
                message: "expected variable identifier".to_string(),
                span: scanner.line_and_column(),
            });
        }

        if variable_name
            .chars()
            .next()
            .expect("the length of the string has already been checked")
            .is_uppercase()
        {
            bail!(ParserError {
                message: "expected variable identifier, got type identifier".to_string(),
                span: scanner.line_and_column(),
            });
        }

        Ok(VariableName::new(variable_name))
    }
}

/// <vexp> ::= <fval> | <vexp> <fval>
impl Parsable for Expression {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let head = ExpressionValue::parse(scanner).context("failed to parse expression value")?;
        if !scanner.is_at_end() && !TERMINATING_CHARACTERS.contains(scanner.current_char()?) {
            let Expression { values: tail } =
                Expression::parse(scanner).context("failed to parse remaining expression")?;
            Ok(Expression {
                values: LinkedList::cons(head, tail),
            })
        } else {
            Ok(Expression {
                values: Box::new(LinkedList::singleton(head)),
            })
        }
    }
}

/// <fval> ::= '\' <decl> '.' <fval> | <val> | <tname> <spec>
impl Parsable for ExpressionValue {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        if *scanner.current_char()? == '\\' {
            scanner
                .advance_and_skip_whitespace()
                .context("failed to advance after '\\' in lambda")?;

            let declaration = StructFieldTypeDeclaration::parse(scanner)
                .context("failed to parse lambda parameter")?;

            scanner
                .expect_character('.', "expected `.` in lambda definition".to_string())
                .context("invalid lambda syntax")?;
            scanner.skip_whitespace();

            let function_body =
                ExpressionValue::parse(scanner).context("failed to parse lambda body")?;

            Ok(Self::FunctionDeclaration(
                declaration,
                Box::new(function_body),
            ))
        } else if scanner.current_char()?.is_uppercase() {
            let type_name =
                TypeName::parse(scanner).context("failed to parse type name in type expression")?;
            let spec = Spec::parse(scanner)
                .with_context(|| format!("failed to parse spec for type '{}'", type_name))?;
            Ok(Self::TypeExpression(type_name, spec))
        } else {
            Value::parse(scanner)
                .map(Self::ValueExpression)
                .context("failed to parse value expression")
        }
    }
}

/// <val> ::= <vname> | '(' <vexp> {',' <vexp>} ')' | <val> '.' <vname> | <val> '[' <vdef> {',' <vdef>} ['|' <vexp>] ']'
impl Parsable for Value {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        let mut current = if *scanner.current_char()? == '(' {
            scanner
                .advance_and_skip_whitespace()
                .context("failed to advance after '(' in parenthesized expression")?;

            let head =
                Expression::parse(scanner).context("failed to parse first expression in tuple")?;
            let mut tail = Vec::new();

            while *scanner.current_char()? == ',' {
                scanner
                    .advance_and_skip_whitespace()
                    .context("failed to advance after ',' in tuple")?;
                tail.push(Expression::parse(scanner).with_context(|| {
                    format!(
                        "failed to parse expression at position {} in tuple",
                        tail.len() + 1
                    )
                })?);
            }

            scanner
                .expect_character(
                    ')',
                    "expected `)` at the end of parenthesized expression".to_string(),
                )
                .context("parenthesized expression not properly closed")?;
            scanner.skip_whitespace();

            if tail.is_empty() {
                Self::Expression(head)
            } else {
                Self::Tuple(NonEmpty { head, tail })
            }
        } else {
            Self::Variable(VariableName::parse(scanner).context("failed to parse variable name")?)
        };

        loop {
            if scanner.is_at_end() {
                break;
            }
            match scanner.current_char()? {
                '.' => {
                    scanner
                        .advance_and_skip_whitespace()
                        .context("failed to advance after '.' in struct access")?;
                    let variable_name = VariableName::parse(scanner)
                        .context("failed to parse field name in struct access")?;
                    current = Self::StructAccess(Box::new(current), variable_name);
                }
                '[' => {
                    scanner
                        .advance_and_skip_whitespace()
                        .context("failed to advance after '[' in case expression")?;

                    let head = VariableDeclaration::parse(scanner)
                        .context("failed to parse first case branch")?;
                    let mut tail = Vec::new();

                    while *scanner.current_char()? == ',' {
                        scanner
                            .advance_and_skip_whitespace()
                            .context("failed to advance after ',' in case expression")?;
                        tail.push(VariableDeclaration::parse(scanner).with_context(|| {
                            format!("failed to parse case branch at position {}", tail.len() + 1)
                        })?);
                    }

                    let expression = if *scanner.current_char()? == '|' {
                        scanner
                            .advance_and_skip_whitespace()
                            .context("failed to advance after '|' in case expression")?;
                        Some(
                            Expression::parse(scanner)
                                .context("failed to parse default case expression")?,
                        )
                    } else {
                        None
                    };

                    current = Self::Case(Box::new(current), NonEmpty { head, tail }, expression);
                    scanner
                        .expect_character(']', "expected `]` after a case expression".to_string())
                        .context("case expression not properly closed")?;
                    scanner.skip_whitespace();
                }
                _ => {
                    scanner.skip_whitespace();
                    break;
                }
            }
        }
        Ok(current)
    }
}

/// <spec> ::= '[' (<vdef> | <vname>) ']' | '{' [<vdef> {',' <vdef>}] '}'
impl Parsable for Spec {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        match scanner.current_char()? {
            '[' => UnionValue::parse(scanner)
                .map(Self::UnionValue)
                .context("failed to parse union value"),
            '{' => {
                scanner
                    .advance_and_skip_whitespace()
                    .context("failed to advance after '{' in struct value")?;

                if *scanner.current_char()? == '}' {
                    scanner
                        .advance_and_skip_whitespace()
                        .context("failed to advance after '}' in empty struct")?;
                    return Ok(Self::StructValue(Vec::new()));
                }

                let mut struct_values = Vec::new();
                struct_values.push(
                    VariableDeclaration::parse(scanner)
                        .context("failed to parse first struct field value")?,
                );

                while *scanner.current_char()? == ',' {
                    scanner
                        .advance_and_skip_whitespace()
                        .context("failed to advance after ',' in struct value")?;
                    struct_values.push(VariableDeclaration::parse(scanner).with_context(|| {
                        format!(
                            "failed to parse struct field value at position {}",
                            struct_values.len()
                        )
                    })?);
                }

                scanner
                    .expect_character(
                        '}',
                        "expected `}` at the end of a struct value declaration".to_string(),
                    )
                    .context("struct value not properly closed")?;
                scanner.skip_whitespace();
                Ok(Self::StructValue(struct_values))
            }
            _ => Err(ParserError {
                message: "unexpected character for start of value spec".to_string(),
                span: scanner.line_and_column(),
            }
            .into()),
        }
    }
}

/// '[' (<vdef> | <vname>) ']'
impl Parsable for UnionValue {
    fn parse(scanner: &mut Scanner) -> Result<Self> {
        scanner
            .expect_character('[', "expected `[` at the start of union value".to_string())
            .context("invalid union value syntax")?;
        scanner.skip_whitespace();

        let variable_name =
            VariableName::parse(scanner).context("failed to parse union value name")?;

        let result = if *scanner.current_char()? == '=' {
            scanner
                .advance_and_skip_whitespace()
                .context("failed to advance after '=' in union value")?;
            let variable_definition = Expression::parse(scanner).with_context(|| {
                format!(
                    "failed to parse value for union element '{}'",
                    variable_name
                )
            })?;
            let variable_declaration = VariableDeclaration {
                variable_name,
                variable_definition,
            };
            Ok(Self::VariableDeclaration(variable_declaration))
        } else {
            Ok(Self::VariableName(variable_name))
        };

        scanner
            .expect_character(']', "expected `]` at the end of union value".to_string())
            .context("union value not properly closed")?;
        scanner.skip_whitespace();
        result
    }
}
