use serde::Serialize;

use crate::{context::OracleCtx, result::OracleResult};

pub trait Oracle<I, O>
where
    O: Serialize,
{
    fn check(&self, input: &I, ctx: &OracleCtx) -> OracleResult<O>;
}
