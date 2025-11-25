use nonempty::NonEmpty;

use crate::{
    ast::{
        Declaration, EnumElementTypeDeclaration, Expression, ExpressionValue, FileName,
        NominalType, Program, Spec, StructFieldTypeDeclaration, TypeDeclaration, TypeDefinition,
        TypeExpression, TypeName, TypeValue, UnionValue, Value, VariableDeclaration, VariableName,
    },
    parser::{ParserError, TERMINATING_CHARACTERS, scanner::Scanner},
};

pub trait Parsable
where
    Self: Sized,
{
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError>;
}

// *******************
// * Top level nodes *
// *******************
/// program is definition sequence
/// <prog> ::= <def> {’,’ <def>}
impl Parsable for Program {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let head = Declaration::parse(scanner)?;

        let mut tail = Vec::new();
        while !scanner.is_at_end() {
            scanner.expect_character(',', "expected `,` between definitions".to_string())?;
            scanner.skip_whitespace();

            let definition = Declaration::parse(scanner)?;
            tail.push(definition);
        }

        let definitions = nonempty::NonEmpty { head, tail };
        Ok(Program { definitions })
    }
}

/// <def> ::= ’@’ <file_name> | <tdef> | <vdef>
impl Parsable for Declaration {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        scanner.skip_whitespace();
        if scanner.is_at_end() {
            Err(ParserError {
                message: "unexpected EOF when parsing declarations".to_string(),
                span: scanner.line_and_column(),
            })
        } else if *scanner.current_char()? == '@' {
            scanner.advance_and_skip_whitespace()?;
            FileName::parse(scanner).map(Self::IncludeDeclaration)
        } else if scanner.current_char()?.is_uppercase() {
            TypeDeclaration::parse(scanner).map(Self::TypeDeclaration)
        } else {
            VariableDeclaration::parse(scanner).map(Self::VariableDeclaration)
        }
    }
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// ’@’ <file_name>
impl Parsable for FileName {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let mut file_name = Vec::new();
        // File name is *very* permissive, so do not use get_chars_until_whitespace.
        while !scanner.is_at_end()
            && !scanner.current_char()?.is_whitespace()
            && *scanner.current_char()? != ','
        {
            file_name.push(*scanner.current_char()?);
            scanner.advance()?;
        }

        if file_name.is_empty() {
            Err(ParserError {
                message: "expected filename".to_string(),
                span: scanner.line_and_column(),
            })
        } else {
            Ok(Self::new(file_name.into_iter().collect::<String>()))
        }
    }
}

// *********
// * Types *
// *********

/// <tdef> ::= <tname> ’=’ ( <tnom> | <texp> ).
impl Parsable for TypeDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let type_name = TypeName::parse(scanner)?;
        if *scanner.current_char()? != '=' {
            return Err(ParserError {
                message: "expected `=` in type declaration".to_string(),
                span: scanner.line_and_column(),
            });
        }
        scanner.advance_and_skip_whitespace()?;

        Ok(Self {
            type_name,
            type_definition: TypeDefinition::parse(scanner)?,
        })
    }
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// <tname>
impl Parsable for TypeName {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        if !scanner.current_char()?.is_uppercase() {
            return Err(ParserError {
                message: "type names must start with an uppercase letter".to_string(),
                span: scanner.line_and_column(),
            });
        }

        let type_name = scanner.get_chars_until_whitespace();
        Ok(TypeName::new(type_name))
    }
}

impl Parsable for TypeDefinition {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        match scanner.current_char()? {
            '[' | '{' => NominalType::parse(scanner).map(Self::NominalType),
            _ => TypeExpression::parse(scanner).map(Self::TypeExpression),
        }
    }
}

/// <tnom> ::= ’{’ <decl> {’,’ <decl>} ’}’ | ’\[’ <elem> {’,’ <elem>} ’\]’
impl Parsable for NominalType {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        match scanner.current_char()? {
            // parsing a struct type
            '{' => {
                scanner.advance_and_skip_whitespace()?;
                let head = StructFieldTypeDeclaration::parse(scanner)?;
                let mut tail = Vec::new();
                while *scanner.current_char()? == ',' {
                    scanner.advance_and_skip_whitespace()?;
                    tail.push(StructFieldTypeDeclaration::parse(scanner)?)
                }
                scanner.expect_character(
                    '}',
                    "expected `}` at the end of struct type declaration".to_string(),
                )?;
                scanner.skip_whitespace();
                Ok(Self::StructType(NonEmpty { head, tail }))
            }
            // parsing a enum type
            '[' => {
                scanner.advance_and_skip_whitespace()?;
                let head = EnumElementTypeDeclaration::parse(scanner)?;
                let mut tail = Vec::new();
                while *scanner.current_char()? == ',' {
                    scanner.advance_and_skip_whitespace()?;
                    tail.push(EnumElementTypeDeclaration::parse(scanner)?)
                }
                scanner.expect_character(
                    ']',
                    "expected `]` at the end of enum type declaration".to_string(),
                )?;
                scanner.skip_whitespace();
                Ok(Self::EnumType(NonEmpty { head, tail }))
            }
            _ => Err(ParserError {
                message: "unexpected character when parsing nominal type".to_string(),
                span: scanner.line_and_column(),
            }),
        }
    }
}

/// field is of given type
/// <decl> ::= <vname> ’:’ <texp>
impl Parsable for StructFieldTypeDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let field_name = VariableName::parse(scanner)?;
        scanner.expect_character(
            ':',
            "expected `:` when parsing field type declaration".to_string(),
        )?;
        scanner.skip_whitespace();
        let type_expression = TypeExpression::parse(scanner)?;
        Ok(Self {
            field_name,
            type_expression,
        })
    }
}

/// simple label or typed field
/// <elem> ::= <vname> [’:’ <texp>]
impl Parsable for EnumElementTypeDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let element_name = VariableName::parse(scanner)?;
        let type_expression = if *scanner.current_char()? == ':' {
            scanner.advance_and_skip_whitespace()?;
            Some(TypeExpression::parse(scanner)?)
        } else {
            None
        };
        Ok(Self {
            element_name,
            type_expression,
        })
    }
}

/// <texp> ::= <tval> | <tval> ’->’ <texp>
impl Parsable for TypeExpression {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let type_value = TypeValue::parse(scanner)?;
        if !scanner.is_at_end()
            && !TERMINATING_CHARACTERS.contains(scanner.current_char()?)
            && *scanner.current_char()? == '-'
        {
            scanner.advance()?;
            scanner
                .expect_character('>', "expected `>` in arrow of type expression".to_string())?;
            scanner.skip_whitespace();
            Ok(Self::FunctionType(
                Box::new(type_value),
                Box::new(TypeExpression::parse(scanner)?),
            ))
        } else {
            Ok(Self::TypeValue(Box::new(type_value)))
        }
    }
}

/// <tval> ::= <tname> | ’(’ <texp> {’,’ <texp>} ’)’
impl Parsable for TypeValue {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        if *scanner.current_char()? == '(' {
            scanner.advance_and_skip_whitespace()?;
            let head = TypeExpression::parse(scanner)?;

            let mut tail = Vec::new();
            while *scanner.current_char()? == ',' {
                scanner.advance_and_skip_whitespace()?;
                tail.push(TypeExpression::parse(scanner)?);
            }

            scanner.expect_character(
                ')',
                "expected `)` after parethesized type expression".to_string(),
            )?;
            scanner.skip_whitespace();

            Ok(Self::TypeTuple(NonEmpty { head, tail }))
        } else {
            TypeName::parse(scanner).map(Self::TypeName)
        }
    }
}

// **********
// * Values *
// **********

/// <vdef> ::= <vname> ’=’ <vexp>
impl Parsable for VariableDeclaration {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let variable_name = VariableName::parse(scanner)?;
        scanner.expect_character('=', "expected `=` in variable declaration".to_string())?;
        scanner.skip_whitespace();
        let variable_definition = Expression::parse(scanner)?;
        Ok(Self {
            variable_name,
            variable_definition,
        })
    }
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// <vname> ’=’ <vexp>
impl Parsable for VariableName {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let variable_name = scanner.get_chars_until_whitespace();
        if variable_name.is_empty() {
            Err(ParserError {
                message: "expected variable identifier".to_string(),
                span: scanner.line_and_column(),
            })
        } else if variable_name
            .chars()
            .next()
            .expect("the length of the string has already been checked")
            .is_uppercase()
        {
            Err(ParserError {
                message: "expected variable identifier, got type identifier".to_string(),
                span: scanner.line_and_column(),
            })
        } else {
            Ok(VariableName::new(variable_name))
        }
    }
}

/// <vexp> ::= <fval> | <vexp> <fval>
impl Parsable for Expression {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let head = ExpressionValue::parse(scanner)?;
        let mut tail = Vec::new();
        while !scanner.is_at_end() && !TERMINATING_CHARACTERS.contains(scanner.current_char()?) {
            tail.push(ExpressionValue::parse(scanner)?);
        }

        Ok(Self {
            values: Box::new(NonEmpty { head, tail }),
        })
    }
}

/// <fval> ::= ’\’ <decl> ’.’ <fval> | <val> | <tname> <spec>
impl Parsable for ExpressionValue {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        if *scanner.current_char()? == '\\' {
            scanner.advance_and_skip_whitespace()?;
            let declaration = StructFieldTypeDeclaration::parse(scanner)?;
            scanner.expect_character('.', "expected `.` in lambda definition".to_string())?;
            scanner.skip_whitespace();
            let function_body = ExpressionValue::parse(scanner)?;
            Ok(Self::FunctionDeclaration(
                declaration,
                Box::new(function_body),
            ))
        } else if scanner.current_char()?.is_uppercase() {
            let type_name = TypeName::parse(scanner)?;
            let spec = Spec::parse(scanner)?;
            Ok(Self::TypeExpression(type_name, spec))
        } else {
            Value::parse(scanner).map(Self::ValueExpression)
        }
    }
}

/// <val> ::= <vname> | ’(’ <vexp> {’,’ <vexp>} ’)’ | <val> ’.’ <vname> | <val> ’[’ <vdef> {’,’ <vdef>} [’|’ <vexp>] ’]’
impl Parsable for Value {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        let mut current = if *scanner.current_char()? == '(' {
            scanner.advance_and_skip_whitespace()?;
            let head = Expression::parse(scanner)?;
            let mut tail = Vec::new();
            while *scanner.current_char()? == ',' {
                scanner.advance_and_skip_whitespace()?;
                tail.push(Expression::parse(scanner)?);
            }
            scanner.expect_character(
                ')',
                "expected `)` at the end of parethesized expression".to_string(),
            )?;
            scanner.skip_whitespace();

            Self::Tuple(NonEmpty { head, tail })
        } else {
            Self::Variable(VariableName::parse(scanner)?)
        };

        loop {
            if scanner.is_at_end() {
                break;
            }
            match scanner.current_char()? {
                '.' => {
                    scanner.advance_and_skip_whitespace()?;
                    let variable_name = VariableName::parse(scanner)?;
                    current = Self::StructAccess(Box::new(current), variable_name);
                }
                '[' => {
                    scanner.advance_and_skip_whitespace()?;
                    let head = VariableDeclaration::parse(scanner)?;

                    let mut tail = Vec::new();
                    while *scanner.current_char()? == ',' {
                        scanner.advance_and_skip_whitespace()?;
                        tail.push(VariableDeclaration::parse(scanner)?);
                    }

                    let expression = if *scanner.current_char()? == '|' {
                        scanner.advance_and_skip_whitespace()?;
                        let result = Expression::parse(scanner)?;
                        Some(result)
                    } else {
                        None
                    };

                    current = Self::Case(Box::new(current), NonEmpty { head, tail }, expression);

                    scanner.expect_character(
                        ']',
                        "expected `]` after a case expression".to_string(),
                    )?;
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

/// <spec> ::= ’[’ (<vdef> | <vname>) ’]’ | ’{’ [<vdef> {’,’ <vdef>}] ’}’
impl Parsable for Spec {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        match scanner.current_char()? {
            '[' => UnionValue::parse(scanner).map(Self::UnionValue),
            '{' => {
                scanner.advance_and_skip_whitespace()?;

                // Empty struct
                if *scanner.current_char()? == '}' {
                    scanner.advance_and_skip_whitespace()?;
                    return Ok(Self::StructValue(Vec::new()));
                }

                let mut struct_values = Vec::new();
                struct_values.push(VariableDeclaration::parse(scanner)?);
                while *scanner.current_char()? == ',' {
                    scanner.advance_and_skip_whitespace()?;
                    struct_values.push(VariableDeclaration::parse(scanner)?);
                }

                scanner.expect_character(
                    '}',
                    "expected `}` at the end of a struct value declaration".to_string(),
                )?;
                scanner.skip_whitespace();

                Ok(Self::StructValue(struct_values))
            }
            _ => Err(ParserError {
                message: "unexpected character for start of value spec".to_string(),
                span: scanner.line_and_column(),
            }),
        }
    }
}

/// ’[’ (<vdef> | <vname>) ’]’
impl Parsable for UnionValue {
    fn parse(scanner: &mut Scanner) -> Result<Self, ParserError> {
        scanner.expect_character('[', "expected `[` at the start of union value".to_string())?;
        scanner.skip_whitespace();

        let variable_name = VariableName::parse(scanner)?;
        let result = if *scanner.current_char()? == '=' {
            scanner.advance_and_skip_whitespace()?;
            let variable_definition = Expression::parse(scanner)?;
            let variable_declaration = VariableDeclaration {
                variable_name,
                variable_definition,
            };
            Ok(Self::VariableDeclaration(variable_declaration))
        } else {
            Ok(Self::VariableName(variable_name))
        };

        scanner.expect_character(']', "expected `]` at the end of union value".to_string())?;
        scanner.skip_whitespace();

        result
    }
}
