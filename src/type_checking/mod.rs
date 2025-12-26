use core::fmt::Display;
use std::collections::HashMap;

use crate::{
    ast::{Program, TypeName, VariableName},
    type_checking::{constraint_solving::solve_constraints, type_inference::generate_constraints},
    util::LinkedList,
};
use anyhow::{Context, Result, bail};
use thiserror::Error;

mod constraint_solving;
mod type_inference;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVar(usize);

impl Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_typevar_{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub enum TypeUnderConstruction {
    Struct(TypeNameOrPlaceholder, Vec<StructField>),
    Union(TypeNameOrPlaceholder, Vec<UnionMember>),
    Tuple(Vec<TypeUnderConstruction>),
    Function(Box<LinkedList<TypeUnderConstruction>>),
    RecurseMarker(TypeName),
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
            TypeUnderConstruction::Function(args) => {
                write!(
                    f,
                    "({})",
                    args.iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(" -> "),
                )
            }
            TypeUnderConstruction::RecurseMarker(type_symbol) => write!(f, "{}<-", type_symbol),
            TypeUnderConstruction::Var(var) => write!(f, "_{}", var),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Struct(TypeName, Vec<StructField>),
    Union(TypeName, Vec<UnionMember>),
    Tuple(Vec<Type>),
    Function(Box<LinkedList<Type>>),
    RecurseMarker(TypeName),
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
            Self::Function(args) => {
                write!(
                    f,
                    "({})",
                    args.iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(" -> "),
                )
            }
            Self::RecurseMarker(type_symbol) => write!(f, "{}<-", type_symbol),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: VariableName,
    pub field_type: TypeUnderConstruction,
}
#[derive(Debug, Clone)]
pub enum UnionMember {
    SingletonUnionMember(VariableName),
    UnionMember(VariableName, TypeUnderConstruction),
}

#[derive(Debug, Clone)]
pub enum TypeNameOrPlaceholder {
    Symbol(TypeName),
    Placeholder,
}

impl Display for TypeNameOrPlaceholder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeNameOrPlaceholder::Symbol(type_symbol) => write!(f, "{}", type_symbol.as_str()),
            TypeNameOrPlaceholder::Placeholder => write!(f, "_"),
        }
    }
}

impl PartialEq for TypeNameOrPlaceholder {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Symbol(a), Self::Symbol(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for TypeNameOrPlaceholder {}

impl From<TypeName> for TypeNameOrPlaceholder {
    fn from(value: TypeName) -> Self {
        TypeNameOrPlaceholder::Symbol(value)
    }
}

impl UnionMember {
    pub fn name(&self) -> &VariableName {
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

impl PartialEq for TypeUnderConstruction {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Struct(l0, _), Self::Struct(r0, _)) => l0 == r0,
            (Self::Union(l0, _), Self::Union(r0, _)) => l0 == r0,
            (Self::Tuple(l0), Self::Tuple(r0)) => l0 == r0,
            (Self::Function(l0), Self::Function(r0)) => {
                l0.len() == r0.len() && l0.iter().zip(r0.iter()).all(|(a, b)| a == b)
            }
            (Self::RecurseMarker(l0), Self::RecurseMarker(r0)) => l0 == r0,
            (Self::Var(l0), Self::Var(r0)) => l0 == r0,
            (Self::RecurseMarker(l0), Self::Struct(TypeNameOrPlaceholder::Symbol(r0), _))
            | (Self::Struct(TypeNameOrPlaceholder::Symbol(l0), _), Self::RecurseMarker(r0)) => {
                l0 == r0
            }
            (Self::RecurseMarker(l0), Self::Union(TypeNameOrPlaceholder::Symbol(r0), _))
            | (Self::Union(TypeNameOrPlaceholder::Symbol(l0), _), Self::RecurseMarker(r0)) => {
                l0 == r0
            }
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Constraint {
    Equal(TypeUnderConstruction, TypeUnderConstruction),
    Subtype(TypeUnderConstruction, TypeUnderConstruction),
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

    fn print_constraints(constraints: &[Constraint]) {
        for constraint in constraints {
            Self::print_constraint(constraint);
        }
    }

    fn print_constraint(constraint: &Constraint) {
        let constraint = match constraint {
            Constraint::Equal(a, b) => {
                format!("{} == {}", a, b)
            }
            Constraint::Subtype(a, b) => {
                format!("{} <= {}", a, b)
            }
        };
        println!("{}", constraint);
    }

    fn add_constraint(&mut self, constraint: Constraint) -> Result<()> {
        match constraint {
            Constraint::Equal(a, b) if is_pure_type(&a) && is_pure_type(&b) => {
                if a == b {
                    Ok(())
                } else {
                    bail!("Types differ: {} and {}", a, b)
                }
            }
            Constraint::Subtype(a, b) if is_pure_type(&a) && is_pure_type(&b) => {
                if a == b {
                    Ok(())
                } else {
                    bail!("{} is not a subtype of {}'", a, b)
                }
            }
            _ => {
                self.constraints.push(constraint);
                Ok(())
            }
        }
    }
}

fn is_pure_type(ty: &TypeUnderConstruction) -> bool {
    match ty {
        TypeUnderConstruction::Var(_) => false,
        TypeUnderConstruction::Struct(_, _)
        | TypeUnderConstruction::Union(_, _)
        | TypeUnderConstruction::RecurseMarker(_) => true,
        TypeUnderConstruction::Tuple(elements) => elements.iter().all(is_pure_type),
        TypeUnderConstruction::Function(args) => args.iter().all(is_pure_type),
    }
}

#[derive(Debug, Clone, Error)]
enum TypeError {
    #[error("Cannot find type in scope")]
    UnableToFindType,
}

pub type TypeMap = HashMap<TypeMapSymbol, Type>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeMapSymbol {
    TypeSymbol(TypeName),
    VariableSymbol(VariableName),
}

impl Display for TypeMapSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeSymbol(type_symbol) => write!(f, "{}", type_symbol.as_str()),
            Self::VariableSymbol(variable_symbol) => write!(f, "{}", variable_symbol.as_str()),
        }
    }
}

impl From<VariableName> for TypeMapSymbol {
    fn from(value: VariableName) -> Self {
        TypeMapSymbol::VariableSymbol(value)
    }
}

impl From<TypeName> for TypeMapSymbol {
    fn from(value: TypeName) -> Self {
        TypeMapSymbol::TypeSymbol(value)
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
                TypeNameOrPlaceholder::Symbol(type_symbol) => {
                    Ok(Type::Struct(type_symbol, struct_fields))
                }
                TypeNameOrPlaceholder::Placeholder => {
                    panic!("We should never encounter placeholders. This is a bug!")
                }
            }
        }
        TypeUnderConstruction::Union(symbol_or_placeholder, union_members) => {
            match symbol_or_placeholder {
                TypeNameOrPlaceholder::Symbol(type_symbol) => {
                    Ok(Type::Union(type_symbol, union_members))
                }
                TypeNameOrPlaceholder::Placeholder => {
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
        TypeUnderConstruction::Function(args) => {
            let args = args
                .into_iter()
                .map(|elm| apply_substitution(elm.clone(), substitutions))
                .collect::<Result<Vec<_>, _>>()?;

            Ok(Type::Function(Box::new(args.try_into().expect(
                "Args cannot be empty, as we just converted it from a linked list.",
            ))))
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
