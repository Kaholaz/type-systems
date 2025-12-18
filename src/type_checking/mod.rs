use core::fmt::Display;
use std::collections::HashMap;

use crate::{
    ast::{Program, TypeName, VariableName},
    type_checking::{constraint_solving::solve_constraints, type_inference::generate_constraints},
    util::LinkedList,
};
use anyhow::{Context, Result};
use thiserror::Error;

mod constraint_solving;
mod type_inference;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeSymbol {
    name: String,
}

impl Display for TypeSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.name)
    }
}

impl From<TypeName> for TypeSymbol {
    fn from(value: TypeName) -> Self {
        TypeSymbol {
            name: value.as_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableSymbol {
    name: String,
}

impl From<VariableName> for VariableSymbol {
    fn from(value: VariableName) -> Self {
        VariableSymbol {
            name: value.as_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVar(usize);

#[derive(Debug, Clone)]
pub enum TypeOrVar {
    Concrete(TypeUnderConstruction),
    Var(TypeVar),
}

#[derive(Debug, Clone)]
pub enum TypeUnderConstruction {
    Struct(SymbolOrPlaceholder, Vec<StructField>),
    Union(SymbolOrPlaceholder, Vec<UnionMember>),
    Tuple(Vec<TypeUnderConstruction>),
    Function(
        Box<LinkedList<TypeUnderConstruction>>,
        Box<TypeUnderConstruction>,
    ),
    RecurseMarker(TypeSymbol),
    Var(TypeVar),
}

impl Display for TypeUnderConstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeUnderConstruction::Struct(symbol_or_placeholder, _) => {
                write!(f, "{}{{}}", symbol_or_placeholder)
            }
            TypeUnderConstruction::Union(symbol_or_placeholder, _) => {
                write!(f, "{}[]", symbol_or_placeholder)
            }
            TypeUnderConstruction::Tuple(elms) => {
                write!(
                    f,
                    "({})",
                    elms.iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeUnderConstruction::Function(args, return_type) => {
                write!(
                    f,
                    "({}) -> {}",
                    args.iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    return_type
                )
            }
            TypeUnderConstruction::RecurseMarker(type_symbol) => write!(f, "{}<-", type_symbol),
            TypeUnderConstruction::Var(var) => write!(f, "_{:?}", var),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Struct(TypeSymbol, Vec<StructField>),
    Union(TypeSymbol, Vec<UnionMember>),
    Tuple(Vec<Type>),
    Function(Box<LinkedList<Type>>, Box<Type>),
    RecurseMarker(TypeSymbol),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Struct(symbol_or_placeholder, _) => {
                write!(f, "{}{{}}", symbol_or_placeholder)
            }
            Self::Union(symbol_or_placeholder, _) => {
                write!(f, "{}[]", symbol_or_placeholder)
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
            Self::Function(args, return_type) => {
                write!(
                    f,
                    "({}) -> {}",
                    args.iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    return_type
                )
            }
            Self::RecurseMarker(type_symbol) => write!(f, "{}<-", type_symbol),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: VariableSymbol,
    pub field_type: TypeUnderConstruction,
}
#[derive(Debug, Clone)]
pub enum UnionMember {
    SingletonUnionMember(VariableSymbol),
    UnionMember(VariableSymbol, TypeUnderConstruction),
}

#[derive(Debug, Clone)]
pub enum SymbolOrPlaceholder {
    Symbol(TypeSymbol),
    Placeholder,
}

impl Display for SymbolOrPlaceholder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymbolOrPlaceholder::Symbol(type_symbol) => write!(f, "{}", type_symbol.name),
            SymbolOrPlaceholder::Placeholder => write!(f, "_"),
        }
    }
}

impl PartialEq for SymbolOrPlaceholder {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Symbol(a), Self::Symbol(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for SymbolOrPlaceholder {}

impl From<TypeSymbol> for SymbolOrPlaceholder {
    fn from(value: TypeSymbol) -> Self {
        SymbolOrPlaceholder::Symbol(value)
    }
}

impl From<TypeName> for SymbolOrPlaceholder {
    fn from(value: TypeName) -> Self {
        SymbolOrPlaceholder::Symbol(value.into())
    }
}

impl UnionMember {
    pub fn name(&self) -> &VariableSymbol {
        match self {
            UnionMember::SingletonUnionMember(symbol) => symbol,
            UnionMember::UnionMember(symbol, _) => symbol,
        }
    }
    pub fn member_type(&self) -> Option<&TypeUnderConstruction> {
        match self {
            UnionMember::SingletonUnionMember(_) => None,
            UnionMember::UnionMember(_, type_) => Some(type_),
        }
    }

    pub fn member_type_owned(self) -> Option<TypeUnderConstruction> {
        match self {
            UnionMember::SingletonUnionMember(_) => None,
            UnionMember::UnionMember(_, type_) => Some(type_),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Equal(TypeOrVar, TypeOrVar),
    Subtype(TypeOrVar, TypeOrVar),
}

pub struct ConstraintContext {
    next_var: usize,
    constraints: Vec<Constraint>,
}

impl ConstraintContext {
    fn new() -> Self {
        Self {
            next_var: 0,
            constraints: Vec::new(),
        }
    }

    fn fresh_var(&mut self) -> TypeVar {
        let var = TypeVar(self.next_var);
        self.next_var += 1;
        var
    }
    fn tov_to_ty(tov: &TypeOrVar) -> TypeUnderConstruction {
        match tov {
            TypeOrVar::Concrete(ty) => ty.clone(),
            TypeOrVar::Var(var) => TypeUnderConstruction::Var(var.clone()),
        }
    }

    fn print_constraints(constraints: &[Constraint]) {
        for constraint in constraints {
            Self::print_constraint(constraint);
        }
    }

    fn print_constraint(constraint: &Constraint) {
        let constraint = match constraint {
            Constraint::Equal(a, b) => {
                format!("{} == {}", Self::tov_to_ty(a), Self::tov_to_ty(b))
            }
            Constraint::Subtype(a, b) => {
                format!("{} <= {}", Self::tov_to_ty(a), Self::tov_to_ty(b))
            }
        };
        println!("{}", constraint);
    }

    fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }
}

#[derive(Debug, Clone, Error)]
pub enum TypeError {
    #[error("Type {0} is not known")]
    UnknownType(TypeSymbol),

    #[error("Variable {0:?} is not known")]
    UnknownVariable(VariableSymbol),

    #[error("Type {0} is already defined")]
    DuplicateTypeDefinition(TypeSymbol),
    #[error("Variable {0:?} is already defined")]
    DuplicateVariableDefinition(VariableSymbol),
    #[error("Encountered an unconstructable infinite type")]
    UnconstructableInfiniteType,

    #[error("Unification error")]
    UnificationError,

    #[error("Cannot find type in scope")]
    UnableToFindType,

    #[error("Illegal function arity (attempted to apply a non function as a function)")]
    IllegalArity,

    #[error("Function arity mismatch: expected {expected} arguments, got {found}")]
    FunctionArityMismatch { expected: usize, found: usize },

    #[error("Tuple size mismatch: expected {expected} elements, got {found}")]
    TupleSizeMismatch { expected: usize, found: usize },

    #[error("Struct name mismatch: cannot unify '{left}' with '{right}'")]
    StructNameMismatch {
        left: SymbolOrPlaceholder,
        right: SymbolOrPlaceholder,
    },

    #[error("Union name mismatch: cannot unify '{left}' with '{right}'")]
    UnionNameMismatch {
        left: SymbolOrPlaceholder,
        right: SymbolOrPlaceholder,
    },

    #[error("Not all strut fields specified when constructing a struct")]
    NotAllStructFieldsSpecified,

    #[error("Cannot construct")]
    CannotConstruct,

    #[error("Union variant does not exist")]
    VariantDoesNotExist,

    #[error("Attempted to access a struct field of a non-struct")]
    StructAccessOfNonStruct,

    #[error("Cannot unify incompatible types:\n  Type 1: {left}\n  Type 2: {right}")]
    IncompatibleTypes {
        left: TypeUnderConstruction,
        right: TypeUnderConstruction,
    },
}

pub type TypeMap = HashMap<TypeMapSymbol, Type>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeMapSymbol {
    TypeSymbol(TypeSymbol),
    VariableSymbol(VariableSymbol),
}

impl Display for TypeMapSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeSymbol(type_symbol) => write!(f, "{}", type_symbol.name),
            Self::VariableSymbol(variable_symbol) => write!(f, "{}", variable_symbol.name),
        }
    }
}

impl From<VariableSymbol> for TypeMapSymbol {
    fn from(value: VariableSymbol) -> Self {
        TypeMapSymbol::VariableSymbol(value)
    }
}

impl From<TypeSymbol> for TypeMapSymbol {
    fn from(value: TypeSymbol) -> Self {
        TypeMapSymbol::TypeSymbol(value)
    }
}

impl From<VariableName> for TypeMapSymbol {
    fn from(value: VariableName) -> Self {
        Into::<VariableSymbol>::into(value).into()
    }
}

impl From<TypeName> for TypeMapSymbol {
    fn from(value: TypeName) -> Self {
        Into::<TypeSymbol>::into(value).into()
    }
}

pub fn type_check(program: &Program) -> Result<TypeMap> {
    let (type_map, constraints) = generate_constraints(program)?;
    let substutions = solve_constraints(constraints)?;
    apply_substitutions(type_map, substutions)
}

fn apply_substitutions(
    type_map: HashMap<TypeMapSymbol, TypeUnderConstruction>,
    substitutions: HashMap<TypeVar, TypeUnderConstruction>,
) -> Result<TypeMap> {
    type_map
        .into_iter()
        .try_fold(TypeMap::new(), |mut map, item| {
            let (symbol, ty) = item;
            let new = apply_substitution(ty, &substitutions)?;
            map.insert(symbol, new);
            Ok(map)
        })
}

fn apply_substitution(
    ty: TypeUnderConstruction,
    substitutions: &HashMap<TypeVar, TypeUnderConstruction>,
) -> Result<Type> {
    match ty {
        TypeUnderConstruction::Struct(symbol_or_placeholder, struct_fields) => {
            match symbol_or_placeholder {
                SymbolOrPlaceholder::Symbol(type_symbol) => {
                    Ok(Type::Struct(type_symbol, struct_fields))
                }
                SymbolOrPlaceholder::Placeholder => {
                    panic!("We should never encounter placeholders. This is a bug!")
                }
            }
        }
        TypeUnderConstruction::Union(symbol_or_placeholder, union_members) => {
            match symbol_or_placeholder {
                SymbolOrPlaceholder::Symbol(type_symbol) => {
                    Ok(Type::Union(type_symbol, union_members))
                }
                SymbolOrPlaceholder::Placeholder => {
                    panic!("We should never encounter placeholders. This is a bug!")
                }
            }
        }
        TypeUnderConstruction::Tuple(elements) => {
            let elements = elements
                .into_iter()
                .map(|elm| apply_substitution(elm, substitutions))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type::Tuple(elements))
        }
        TypeUnderConstruction::Function(args, return_value) => {
            let args = args
                .into_iter()
                .map(|elm| apply_substitution(elm.clone(), substitutions))
                .collect::<Result<Vec<_>, _>>()?;
            let return_value = apply_substitution(*return_value, substitutions)?;

            Ok(Type::Function(
                Box::new(
                    args.try_into().expect(
                        "Args cannot be empty, as we just converted it from a linked list.",
                    ),
                ),
                Box::new(return_value),
            ))
        }
        TypeUnderConstruction::RecurseMarker(symbol) => Ok(Type::RecurseMarker(symbol)),
        TypeUnderConstruction::Var(type_var) => {
            let ty = substitutions
                .get(&type_var)
                .ok_or(TypeError::UnableToFindType)?;
            apply_substitution(ty.clone(), substitutions)
                .with_context(|| format!("while resolving type variable {:?}={:?}", type_var, ty))
        }
    }
}
