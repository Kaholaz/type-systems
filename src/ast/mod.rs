/// This module defines AST nodes for the grammar. The grammar is defined in this way:
///
/// <prog> ::= <def> {’,’ <def>}. // program is definition sequence
/// <def> ::= ’@’ <file_name> // include defs from specified file
/// | <tdef> // type definition
/// | <vdef>. // value definition
/// <tdef> ::= <tname> ’=’ ( <tnom> // specify name of nominal type
/// | <texp> ). // ... or structural type
/// <tnom> ::= ’{’ <decl> {’,’ <decl>} ’}’ // type of struct
/// | ’[’ <elem> {’,’ <elem>} ’]’. // type of union
/// <decl> ::= <vname> ’:’ <texp>. // field is of given type
/// <elem> ::= <vname> [’:’ <texp>]. // simple label or typed field
/// <texp> ::= <tval>
/// | <tval> ’->’ <texp>. // type of a function
/// <tval> ::= <tname> // name of type
/// | ’(’ <texp> {’,’ <texp>} ’)’. // tuple type or parenth
/// <vdef> ::= <vname> ’=’ <vexp>. // specify name of a value
/// <vexp> ::= <fval>
/// | <vexp> <fval>. // function application
/// <fval> ::= ’\’ <decl> ’.’ <fval> // function definition (lambda)
/// | <val>
/// | <tname> <spec>. // create or take value of type
/// <val> ::= <vname> // content of variable (named value)
/// | ’(’ <vexp> {’,’ <vexp>} ’)’ // tuple or parentheses
/// | <val> ’.’ <vname> // access field of tuple or struct
/// | <val> ’[’ <vdef> {’,’ <vdef>} [’|’ <vexp>] ’]’. // case
/// <spec> ::= ’[’ (<vdef> | <vname>) ’]’ // union value
/// | ’{’ [<vdef> {’,’ <vdef>}] ’}’. // struct field values
use nonempty::NonEmpty;

// *******************
// * Top level nodes *
// *******************
/// program is definition sequence
/// <prog> ::= <def> {’,’ <def>}
pub struct Program {
    pub definitions: NonEmpty<Definition>,
}

/// <def> ::= ’@’ <file_name> | <tdef> | <vdef>
pub enum Definition {
    IncludeDefinition(FileName),
    TypeDefinition(TypeDeclaration),
    ValueDefinition(VariableDeclaration),
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// ’@’ <file_name>
pub type FileName = String;

// *********
// * Types *
// *********

/// <tdef> ::= <tname> ’=’ ( <tnom> | <texp> ).
pub struct TypeDeclaration {
    /// <tname>
    pub type_name: TypeName,

    /// ( <tnom> | <texp> )
    pub type_definition: TypeDefinition,
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// <tname> ’=’ <tnom> | <texp>
pub type TypeName = String;

/// <tnom> | <texp>
pub enum TypeDefinition {
    /// specify name of nominal type
    /// <tnom>
    NominalType(NominalType),

    /// ... or structural type
    /// <texp>
    TypeExpression(TypeExpression),
}

/// <tnom> ::= ’{’ <decl> {’,’ <decl>} ’}’ | ’\[’ <elem> {’,’ <elem>} ’\]’
pub enum NominalType {
    /// type of struct
    /// ’{’ <decl> {’,’ <decl>} ’}’
    StructType(NonEmpty<FieldTypeDeclaration>),

    /// type of union
    /// ’\[’ <elem> {’,’ <elem>} ’\]’
    EnumType(NonEmpty<EnumElementTypeDeclaration>),
}

/// field is of given type
/// <decl> ::= <vname> ’:’ <texp>
pub struct FieldTypeDeclaration {
    pub field_name: VariableName,
    pub type_expression: TypeExpression,
}

/// simple label or typed field
/// <elem> ::= <vname> [’:’ <texp>]
pub struct EnumElementTypeDeclaration {
    pub element_name: VariableName,
    pub type_expression: Option<TypeExpression>,
}

/// <texp> ::= <tval> | <tval> ’->’ <texp>
pub enum TypeExpression {
    /// <tval>
    TypeValue(Box<TypeValue>),
    /// type of a function
    /// <tval> ’->’ <texp>
    FunctionType(Box<TypeValue>, Box<TypeExpression>),
}

/// <tval> ::= <tname> | ’(’ <texp> {’,’ <texp>} ’)’
pub enum TypeValue {
    /// name of type
    /// <tname>
    TypeName(TypeName),

    /// tuple type or parenth
    /// ’(’ <texp> {’,’ <texp>} ’)’
    TypeTuple(NonEmpty<TypeExpression>),
}

// **********
// * Values *
// **********

/// <vdef> ::= <vname> ’=’ <vexp>
pub struct VariableDeclaration {
    pub variable_name: VariableName,
    pub variable_definition: Expression,
}

/// The nonterminals <tname> (type name), <vname> (value name) and <file_name> are not specified in the syntax
/// <vname> ’=’ <vexp>
pub type VariableName = String;

/// <vexp> ::= <fval> | <vexp> <fval>
pub enum Expression {
    /// <fval>
    FunctionValue(Box<FunctionValue>),

    // function application
    /// <vexp> <fval>
    FunctionApplication(Box<Expression>, Box<FunctionValue>),
}

/// <fval> ::= ’\’ <decl> ’.’ <fval> | <val> | <tname> <spec>
pub enum FunctionValue {
    /// function definition (lambda)
    /// ’\’ <decl> ’.’ <fval>
    FunctionDeclaration(FieldTypeDeclaration, Box<FunctionValue>),

    /// <val>
    ValueExpression(Value),

    /// create or take value of type
    /// <tname> <spec>
    TypeExpression(TypeName, Spec),
}

/// <val> ::= <vname> | ’(’ <vexp> {’,’ <vexp>} ’)’ | <val> ’.’ <vname> | <val> ’[’ <vdef> {’,’ <vdef>} [’|’ <vexp>] ’]’
pub enum Value {
    /// content of variable (named value)
    /// <vname>
    Variable(VariableName),

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
pub enum Spec {
    /// union value
    /// ’[’ (<vdef> | <vname>) ’]’
    UnionValue(UnionValue),

    /// struct field values
    /// ’{’ [<vdef> {’,’ <vdef>}] ’}’
    StructFieldValue(NonEmpty<VariableDeclaration>), // Box because of recursive structure
}

/// ’[’ (<vdef> | <vname>) ’]’
pub enum UnionValue {
    /// <vdef>
    VariableDeclaration(VariableDeclaration),

    // <vname>
    VariableName(VariableName),
}
