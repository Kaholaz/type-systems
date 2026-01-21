use std::fmt::Display;

/// This module defines AST nodes for the grammar. The grammar is defined in this way:
///
/// <prog> ::= <def> {’,’ <def>}. // program is definition sequence
/// <def> ::= ’@’ <file_name> // include defs from specified file
///         | <tdef> // type definition
///         | <vdef>. // value definition
/// <tdef> ::= <tname> ’=’ ( <tnom> // specify name of nominal type
///          | <texp> ). // ... or structural type
/// <tnom> ::= ’{’ {<tname> ’,’} <decl> {’,’ <decl>} ’}’ // type of struct
///          | ’[’ {<tname> ’,’} <elem> {’,’ <elem>} ’]’ // type of union
/// <decl> ::= <vname> ’:’ <texp>. // field is of given type
/// <elem> ::= <vname> [’:’ <texp>]. // simple label or typed field
/// <texp> ::= <tval>
///          | <tval> ’->’ <texp>. // type of a function
/// <tval> ::= <tname> [’(’ <texp> {’,’ <texp>} ’)’]
///          | ’(’ <texp> {’,’ <texp>} ’)’. // tuple type or parenth
/// <vdef> ::= <vname> ’=’ <vexp>. // specify name of a value
/// <vexp> ::= <fval>
///          | <vexp> <fval>. // function application
/// <fval> ::= ’\’ <arg> ’.’ <fval> // function definition (lambda)
///          | <val>
///          | <tname> <spec>. // create or take value of type
/// <arg> ::= <vname> [':' <texp>]
/// <val> ::= <vname> // content of variable (named value)
///         | ’(’ <vexp> {’,’ <vexp>} ’)’ // tuple or parentheses
///         | <val> ’.’ <vname> // access field of tuple or struct
///         | <val> ’[’ <vdef> {’,’ <vdef>} [’|’ <vexp>] ’]’. // case
/// <spec> ::= ’[’ (<vdef> | <vname>) ’]’ // union value
///          | ’{’ [<vdef> {’,’ <vdef>}] ’}’. // struct field values
use nonempty::NonEmpty;

use crate::util::LinkedList;

// *******************
// * Top level nodes *
// *******************
/// program is definition sequence
/// <prog> ::= <def> {’,’ <def>}
#[derive(Debug, Clone)]
pub struct Program {
    pub definitions: NonEmpty<Declaration>,
}

/// <def> ::= ’@’ <file_name> | <tdef> | <vdef>
#[derive(Debug, Clone)]
pub enum Declaration {
    IncludeDeclaration(FileName, Box<Program>),
    TypeDeclaration(TypeDeclaration),
    VariableDeclaration(VariableDeclaration),
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// ’@’ <file_name>
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileName(String);
impl FileName {
    pub fn new(s: impl Into<String>) -> Self {
        FileName(s.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Display for FileName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

// *********
// * Types *
// *********

/// <tdef> ::= <tname> [’=’ (<tnom> | <texp>)]. // type spec. optional
#[derive(Debug, Clone)]
pub struct TypeDeclaration {
    /// <tname>
    pub type_name: TypeName,

    /// ['=' ( <tnom> | <texp> )]
    pub type_definition: Option<TypeDefinition>,
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// <tname> ’=’ <tnom> | <texp>
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeName(String);
impl TypeName {
    pub fn new(s: impl Into<String>) -> Self {
        TypeName(s.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn as_string(self) -> String {
        self.0
    }
}

impl Display for TypeName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// <tnom> | <texp>
#[derive(Debug, Clone)]
pub enum TypeDefinition {
    /// specify name of nominal type
    /// <tnom>
    NominalType(NominalType),

    /// ... or structural type
    /// <texp>
    TypeExpression(TypeExpression),
}

/// <tnom> ::= ’{’ {<tname> ’,’} <decl> {’,’ <decl>} ’}’
///          | ’[’ {<tname> ’,’} <elem> {’,’ <elem>} ’]’
#[derive(Debug, Clone)]
pub enum NominalType {
    /// type of struct
    /// ’{’ {<tname> ’,’} <decl> {’,’ <decl>} ’}’
    StructType {
        generics: Vec<TypeName>,
        fields: NonEmpty<StructFieldTypeDeclaration>,
    },

    /// type of union
    /// ’[’ {<tname> ’,’} <elem> {’,’ <elem>} ’]’
    UnionType {
        generics: Vec<TypeName>,
        members: NonEmpty<EnumElementTypeDeclaration>,
    },
}

/// field is of given type
/// <decl> ::= <vname> ’:’ <texp>
#[derive(Debug, Clone)]
pub struct StructFieldTypeDeclaration {
    pub field_name: VariableName,
    pub type_expression: TypeExpression,
}

/// simple label or typed field
/// <elem> ::= <vname> [’:’ <texp>]
#[derive(Debug, Clone)]
pub struct EnumElementTypeDeclaration {
    pub element_name: VariableName,
    pub type_expression: Option<TypeExpression>,
}

/// <texp> ::= <tval> | <tval> ’->’ <texp>
#[derive(Debug, Clone)]
pub enum TypeExpression {
    /// <tval>
    TypeValue(Box<TypeValue>),
    /// type of a function
    /// <tval> ’->’ <texp>
    FunctionType(Box<LinkedList<TypeValue>>),
}

/// <tval> ::= <tname> [’(’ <texp> {’,’ <texp>} ’)’]
///          | ’(’ <texp> {’,’ <texp>} ’)’
#[derive(Debug, Clone)]
pub enum TypeValue {
    /// name of type
    /// <tname> [’(’ <texp> {’,’ <texp>} ’)’]
    TypeName {
        type_name: TypeName,
        generics: Vec<TypeExpression>,
    },

    /// tuple type or parenth
    /// ’(’ <texp> {’,’ <texp>} ’)’
    TypeTuple(NonEmpty<TypeExpression>),
}

// **********
// * Values *
// **********

/// <vdef> ::= <vname> ’=’ <vexp>
#[derive(Debug, Clone)]
pub struct VariableDeclaration {
    pub variable_name: VariableName,
    pub variable_definition: Expression,
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// <vname> ’=’ <vexp>
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableName(String);
impl VariableName {
    pub fn new(s: impl Into<String>) -> Self {
        VariableName(s.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn as_string(self) -> String {
        self.0
    }
}

impl Display for VariableName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// <vexp> ::= <fval> | <vexp> <fval>
#[derive(Debug, Clone)]
pub struct Expression {
    pub values: Box<LinkedList<ExpressionValue>>,
}

/// <fval> ::= ’\’ <arg> ’.’ <fval> | <val> | <tname> <spec>
#[derive(Debug, Clone)]
pub enum ExpressionValue {
    /// function definition (lambda)
    /// ’\’ <arg> ’.’ <fval>
    FunctionDeclaration {
        function_arg: FunctionArgument,
        function_body: Box<ExpressionValue>,
    },

    /// <val>
    ValueExpression(Value),

    /// create or take value of type
    /// <tname> <spec>
    TypeExpression(TypeName, Spec),
}

/// <arg> ::= <vname> [':' <texp>]
#[derive(Debug, Clone)]
pub struct FunctionArgument {
    pub argument_name: VariableName,
    pub type_expression: Option<TypeExpression>,
}

/// <val> ::= <vname> | ’(’ <vexp> {’,’ <vexp>} ’)’ | <val> ’.’ <vname> | <val> ’[’ <vdef> {’,’ <vdef>} [’|’ <vexp>] ’]’
#[derive(Debug, Clone)]
pub enum Value {
    /// content of variable (named value)
    /// <vname>
    Variable(VariableName),

    /// paraenthesesized expression
    /// ’(’ <vexp> ’)’
    Expression(Expression),

    /// tuple or parentheses
    /// ’(’ <vexp> {’,’ <vexp>} ’)’
    Tuple(NonEmpty<Expression>),

    /// access field of tuple or struct
    /// <val> ’.’ <vname>
    StructAccess(Box<Value>, VariableName),

    /// case
    /// <val> ’[’ <vdef> {’,’ <vdef>} [’|’ <vexp>] ’]’
    Case(
        Box<Value>,
        NonEmpty<VariableDeclaration>,
        Option<Expression>,
    ),
}

/// <spec> ::= ’[’ (<vdef> | <vname>) ’]’ | ’{’ [<vdef> {’,’ <vdef>}] ’}’
#[derive(Debug, Clone)]
pub enum Spec {
    /// union value
    /// ’[’ (<vdef> | <vname>) ’]’
    UnionValue(UnionValue),

    /// struct field values (may be empty)
    /// ’{’ [<vdef> {’,’ <vdef>}] ’}’
    StructValue(Vec<VariableDeclaration>),
}

/// ’[’ (<vdef> | <vname>) ’]’
#[derive(Debug, Clone)]
pub enum UnionValue {
    /// <vdef>
    VariableDeclaration(VariableDeclaration),

    // <vname>
    VariableName(VariableName),
}

impl UnionValue {
    pub fn name(&self) -> &VariableName {
        match self {
            UnionValue::VariableDeclaration(VariableDeclaration {
                variable_name,
                variable_definition: _,
            }) => variable_name,
            UnionValue::VariableName(variable_name) => variable_name,
        }
    }
}
