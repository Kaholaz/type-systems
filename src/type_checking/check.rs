use crate::{
    ast::{Expression, ExpressionValue, TypeDefinition, TypeExpression},
    type_checking::{PartialType, TypeEnv, infer::Infer, unification::UnificationContext},
};
use anyhow::Result;

pub trait Check {
    fn check(
        &self,
        env: &TypeEnv,
        ctx: &mut UnificationContext,
        expected: PartialType,
    ) -> Result<()>;
}

impl Check for TypeDefinition {
    fn check(
        &self,
        env: &TypeEnv,
        ctx: &mut UnificationContext,
        expected: PartialType,
    ) -> Result<()> {
        let inferred = self.infer(env, ctx)?;
        ctx.unify_partial(inferred, expected)
    }
}

impl Check for TypeExpression {
    fn check(
        &self,
        env: &TypeEnv,
        ctx: &mut UnificationContext,
        expected: PartialType,
    ) -> Result<()> {
        let inferred = self.infer(env, ctx)?;
        ctx.unify_partial(inferred, expected)
    }
}

impl Check for Expression {
    fn check(
        &self,
        env: &TypeEnv,
        ctx: &mut UnificationContext,
        expected: PartialType,
    ) -> Result<()> {
        let inferred = self.infer(env, ctx)?;
        ctx.unify_partial(inferred, expected)
    }
}

impl Check for ExpressionValue {
    fn check(
        &self,
        env: &TypeEnv,
        ctx: &mut UnificationContext,
        expected: PartialType,
    ) -> Result<()> {
        let inferred = self.infer(env, ctx)?;
        ctx.unify_partial(inferred, expected)
    }
}
