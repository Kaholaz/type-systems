use core::fmt;
use std::error::Error;

mod parsers;
mod scanner;

use crate::{
    ast::Program,
    parser::{
        parsers::Parsable,
        scanner::{LineAndColumn, Scanner},
    },
};
use anyhow::Result;

static RESERVED_CHARACTERS: [char; 11] = ['{', '}', '[', ']', '(', ')', ',', '.', '|', ':', '='];
static TERMINATING_CHARACTERS: [char; 5] = ['}', ']', ')', ',', '|'];

pub fn parse(source: String) -> Result<Program> {
    let mut scanner = Scanner::new(source);
    Program::parse(&mut scanner)
}

#[derive(Debug)]
pub struct ParserError {
    pub message: String,
    pub span: LineAndColumn,
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Parser error at line {}, column {}: {}",
            self.span.line, self.span.column, self.message
        )
    }
}

impl Error for ParserError {}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a scanner from a string
    fn scan(s: &str) -> Scanner {
        Scanner::new(s.to_string())
    }

    // Helper to parse a full program
    fn parse_program(s: &str) -> Result<Program> {
        Program::parse(&mut scan(s))
    }

    // ********************
    // * Basic Type Tests *
    // ********************

    #[test]
    fn test_simple_type_declaration() {
        let result = parse_program("MyType = Int");
        assert!(result.is_ok());
    }

    #[test]
    fn test_struct_type_single_field() {
        let result = parse_program("Point = {x: Int}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_struct_type_multiple_fields() {
        let result = parse_program("Point = {x: Int, y: Int}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_enum_type_simple_labels() {
        let result = parse_program("Color = [red, green, blue]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_enum_type_with_data() {
        let result = parse_program("Option = [some: Int, none]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_function_type() {
        let result = parse_program("Func = Int -> Int");
        assert!(result.is_ok());
    }

    #[test]
    fn test_function_type_nested() {
        let result = parse_program("CurriedFunc = Int -> Int -> Int");
        assert!(result.is_ok());
    }

    #[test]
    fn test_tuple_type() {
        let result = parse_program("Pair = (Int, String)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_tuple_type_single_element_is_parenthesized() {
        let result = parse_program("Single = (Int)");
        assert!(result.is_ok());
    }

    // ***************
    // * Value Tests *
    // ***************

    #[test]
    fn test_simple_variable_definition() {
        let result = parse_program("x = y");
        assert!(result.is_ok());
    }

    #[test]
    fn test_lambda_definition() {
        let result = parse_program("id = \\x: Int. x");
        assert!(result.is_ok());
    }

    #[test]
    fn test_nested_lambda() {
        let result = parse_program("add = \\x: Int. \\y: Int. x");
        assert!(result.is_ok());
    }

    #[test]
    fn test_function_application() {
        let result = parse_program("result = f x");
        assert!(result.is_ok());
    }

    #[test]
    fn test_multiple_function_application() {
        let result = parse_program("result = f x y z");
        assert!(result.is_ok());
    }

    #[test]
    fn test_tuple_value() {
        let result = parse_program("pair = (x, y)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_struct_field_access() {
        let result = parse_program("x = point.x");
        assert!(result.is_ok());
    }

    #[test]
    fn test_chained_field_access() {
        let result = parse_program("x = obj.field1.field2");
        assert!(result.is_ok());
    }

    #[test]
    fn test_struct_value_creation() {
        let result = parse_program("p = Point{x = 10, y = 20}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_struct_value_empty() {
        let result = parse_program("empty = Empty{}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_union_value_simple() {
        let result = parse_program("c = Color[red]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_union_value_with_data() {
        let result = parse_program("opt = Option[some = 42]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_case_expression_simple() {
        let result = parse_program("x = color[red = 1, green = 2, blue = 3]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_case_expression_with_default() {
        let result = parse_program("x = color[red = 1 | 0]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_case_expression_multiple_with_default() {
        let result = parse_program("x = opt[some = val, none = 0 | fallback]");
        assert!(result.is_ok());
    }

    // ************************
    // * Multiple Definitions *
    // ************************

    #[test]
    fn test_multiple_definitions() {
        let result = parse_program("x = 1, y = 2");
        assert!(result.is_ok());
    }

    #[test]
    fn test_mixed_definitions() {
        let result = parse_program("Int = Int, x = 1, Point = {x: Int, y: Int}");
        assert!(result.is_ok());
    }

    // *******************
    // * Include Tests   *
    // *******************

    #[test]
    fn test_include_declaration() {
        let result = parse_program("@stdlib.lang");
        assert!(result.is_ok());
    }

    #[test]
    fn test_include_with_other_declarations() {
        let result = parse_program("@prelude, x = 1");
        assert!(result.is_ok());
    }

    // ********************
    // * Whitespace Tests *
    // ********************

    #[test]
    fn test_whitespace_handling() {
        let result = parse_program("  x   =   y  ");
        assert!(result.is_ok());
    }

    #[test]
    fn test_newlines_as_whitespace() {
        let result = parse_program("x = 1,\ny = 2");
        assert!(result.is_ok());
    }

    #[test]
    fn test_complex_whitespace() {
        let result = parse_program("Point = {\n  x: Int,\n  y: Int\n}");
        assert!(result.is_ok());
    }

    // **************************
    // * Complex/Combined Tests *
    // **************************

    #[test]
    fn test_complex_type_in_struct() {
        let result = parse_program("Func = {f: Int -> Int}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_nested_tuples() {
        let result = parse_program("nested = ((x, y), z)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_lambda_with_application() {
        let result = parse_program("result = (\\x: Int. x) 5");
        assert!(result.is_ok());
    }

    #[test]
    fn test_case_on_field_access() {
        let result = parse_program("x = obj.field[some = val | 0]");
        assert!(result.is_ok());
    }

    // ***************
    // * Error Tests *
    // ***************

    #[test]
    fn test_type_name_must_be_uppercase() {
        let result = parse_program("myType = Int");
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_equals_in_type_def() {
        let result = parse_program("Type Int");
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_equals_in_var_def() {
        let result = parse_program("x y");
        assert!(result.is_err());
    }

    #[test]
    fn test_unclosed_struct_type() {
        let result = parse_program("Point = {x: Int");
        assert!(result.is_err());
    }

    #[test]
    fn test_unclosed_enum_type() {
        let result = parse_program("Color = [Red, Green");
        assert!(result.is_err());
    }

    #[test]
    fn test_unclosed_tuple() {
        let result = parse_program("x = (a, b");
        assert!(result.is_err());
    }

    #[test]
    fn test_unclosed_struct_value() {
        let result = parse_program("p = Point{x = 1");
        assert!(result.is_err());
    }

    #[test]
    fn test_unclosed_union_value() {
        let result = parse_program("c = Color[Red");
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_colon_in_field_decl() {
        let result = parse_program("Point = {x Int}");
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_program() {
        let result = parse_program("");
        assert!(result.is_err());
    }

    // **************
    // * Edge Cases *
    // **************

    #[test]
    fn test_single_char_names() {
        let result = parse_program("x = y");
        assert!(result.is_ok());
    }

    #[test]
    fn test_long_names() {
        let result = parse_program("veryLongVariableName = anotherLongName");
        assert!(result.is_ok());
    }

    #[test]
    fn test_empty_struct_type() {
        let result = parse_program("Empty = {}");
        assert!(result.is_err());
    }

    #[test]
    fn test_deeply_nested_function_types() {
        let result = parse_program("F = Int -> (Int -> (Int -> Int))");
        assert!(result.is_ok());
    }

    #[test]
    fn test_application_with_tuple() {
        let result = parse_program("result = f (x, y)");
        assert!(result.is_ok());
    }

    // **********************************
    // * Additional Comprehensive Tests *
    // **********************************

    #[test]
    fn test_function_type_with_tuple_argument() {
        let result = parse_program("F = (Int, String) -> Bool");
        assert!(result.is_ok());
    }

    #[test]
    fn test_function_type_returning_tuple() {
        let result = parse_program("F = Int -> (Int, Int)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_enum_with_function_payload() {
        let result = parse_program("Callback = [handler: Int -> Int, none]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_lambda_returning_lambda() {
        let result = parse_program("curry = \\f: (Int, Int) -> Int. \\x: Int. \\y: Int. f (x, y)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_nested_case_expressions() {
        let result = parse_program("x = opt[some = inner[left = 1, right = 2] | 0]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_case_with_multiple_clauses_no_default() {
        let result = parse_program("x = val[a = 1, b = 2, c = 3, d = 4]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_struct_with_computed_values() {
        let result = parse_program("p = Point{x = f a, y = g b}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_struct_with_lambda_values() {
        let result = parse_program("funcs = Funcs{f = \\x: Int. x, g = \\y: Int. y}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_union_with_tuple_value() {
        let result = parse_program("pair = Pair[tuple = (1, 2)]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_union_with_struct_value() {
        let result = parse_program("wrapped = Wrapper[point = Point{x = 1, y = 2}]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_deeply_nested_field_access() {
        let result = parse_program("x = obj.a.b.c.d.e.f");
        assert!(result.is_ok());
    }

    #[test]
    fn test_field_access_on_tuple() {
        let result = parse_program("x = (point, other).x");
        assert!(result.is_ok());
    }

    #[test]
    fn test_field_access_on_function_result() {
        let result = parse_program("x = f arg.field");
        assert!(result.is_ok());
    }

    #[test]
    fn test_case_on_function_result() {
        let result = parse_program("x = f arg[some = val | 0]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_multiple_applications_with_parens() {
        let result = parse_program("result = f (g x) (h y)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_application_of_lambda() {
        let result = parse_program("result = (\\x: Int. x) arg");
        assert!(result.is_ok());
    }

    #[test]
    fn test_application_chain_with_field_access() {
        let result = parse_program("result = f x.field y.other");
        assert!(result.is_ok());
    }

    #[test]
    fn test_tuple_of_lambdas() {
        let result = parse_program("funcs = (\\x: Int. x, \\y: String. y)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_tuple_of_applications() {
        let result = parse_program("results = (f x, g y, h z)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_empty_tuple() {
        let result = parse_program("unit = ()");
        assert!(result.is_err());
    }

    #[test]
    fn test_single_element_tuple() {
        let result = parse_program("single = (x)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_multiple_includes() {
        let result = parse_program("@std/prelude, @std/io, @std/math");
        assert!(result.is_ok());
    }

    #[test]
    fn test_include_with_path() {
        let result = parse_program("@../lib/module.lang");
        assert!(result.is_ok());
    }

    #[test]
    fn test_include_with_complex_path() {
        let result = parse_program("@/usr/local/lib/std-v2.1.0/core");
        assert!(result.is_ok());
    }

    #[test]
    fn test_mixed_declarations_complex() {
        let result = parse_program(
            "Bool = [true, false], \
             not = \\b: Bool. b[true = Bool[false], false = Bool[true]], \
             Pair = {fst: Bool, snd: Bool}",
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_realistic_example_option_map() {
        let result = parse_program(
            "Option = [some: Int, none], \
             map = \\f: Int -> Int. \\opt: Option. \
             opt[some = Option[some = f some], none = Option[none]]",
        );
        assert!(result.is_ok());
    }

    // ********************
    // * More Error Tests *
    // ********************

    #[test]
    fn test_variable_name_cannot_be_uppercase() {
        let result = parse_program("X = y");
        // This should fail - uppercase variable name
        assert!(result.is_err());
    }

    #[test]
    fn test_enum_field_cannot_be_uppercase() {
        let result = parse_program("Color = [Red, Green]");
        // Should fail - enum fields must be lowercase
        assert!(result.is_err());
    }

    #[test]
    fn test_struct_field_cannot_be_uppercase() {
        let result = parse_program("Point = {X: Int, Y: Int}");
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_arrow_in_function_type() {
        let result = parse_program("F = Int Int");
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_dot_in_lambda() {
        let result = parse_program("f = \\x: Int x");
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_closing_bracket_in_case() {
        let result = parse_program("x = val[a = 1");
        assert!(result.is_err());
    }

    #[test]
    fn test_double_comma() {
        let result = parse_program("x = 1,, y = 2");
        assert!(result.is_err());
    }

    #[test]
    fn test_trailing_comma_in_definitions() {
        let result = parse_program("x = 1, y = 2,");
        assert!(result.is_ok());
    }

    #[test]
    fn test_missing_type_in_lambda_param() {
        let result = parse_program("f = \\x. x");
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_colon_in_lambda_param() {
        let result = parse_program("f = \\x Int. x");
        assert!(result.is_err());
    }

    #[test]
    fn test_unmatched_opening_paren() {
        let result = parse_program("x = (a, b");
        assert!(result.is_err());
    }

    #[test]
    fn test_unmatched_closing_paren() {
        let result = parse_program("x = a, b)");
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_variable_name() {
        let result = parse_program(" = value");
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_type_name() {
        let result = parse_program(" = Int");
        assert!(result.is_err());
    }

    // ****************
    // * Stress Tests *
    // ****************

    #[test]
    fn test_deeply_nested_types() {
        let result = parse_program("Deep = (((((((((Int)))))))))");
        assert!(result.is_ok());
    }

    #[test]
    fn test_long_function_type_chain() {
        let result = parse_program("F = Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int");
        assert!(result.is_ok());
    }

    #[test]
    fn test_many_tuple_elements() {
        let result = parse_program("big = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)");
        assert!(result.is_ok());
    }

    #[test]
    fn test_many_struct_fields() {
        let result =
            parse_program("Big = {a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int, h: Int}");
        assert!(result.is_ok());
    }

    #[test]
    fn test_many_enum_variants() {
        let result = parse_program("Enum = [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_many_case_branches() {
        let result =
            parse_program("x = val[a = 1, b = 2, c = 3, d = 4, e = 5, f = 6, g = 7, h = 8]");
        assert!(result.is_ok());
    }

    #[test]
    fn test_complex_nested_structure() {
        let result = parse_program("x = Point{x = f (\\a: Int. a.b.c[d = e | g]) h, y = (i, j).k}");
        assert!(result.is_ok());
    }

    // *************************
    // * Whitespace Edge Cases *
    // *************************

    #[test]
    fn test_no_whitespace_around_operators() {
        let result = parse_program("x=y");
        assert!(result.is_ok());
    }

    #[test]
    fn test_tabs_as_whitespace() {
        let result = parse_program("x\t=\ty");
        assert!(result.is_ok());
    }

    #[test]
    fn test_mixed_whitespace() {
        let result = parse_program("x \t= \n\t y");
        assert!(result.is_ok());
    }

    #[test]
    fn test_many_newlines() {
        let result = parse_program("x = y\n\n\n\n, z = w");
        assert!(result.is_ok());
    }
}
