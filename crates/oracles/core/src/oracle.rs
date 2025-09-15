use crate::{context::OracleCtx, result::OracleResult};

pub trait Oracle<I, O> {
  fn name(&self) -> &str;
  fn check(&self, input: I, ctx: &OracleCtx) -> OracleResult<O>;
}

pub struct FnOracle<I, O, F>
where
  F: Fn(I, &OracleCtx) -> OracleResult<O>,
{
  name: String,
  check: F,
  _marker: std::marker::PhantomData<fn(I) -> O>,
}

impl<I, O, F> FnOracle<I, O, F>
where
  F: Fn(I, &OracleCtx) -> OracleResult<O>,
{
  pub fn new(name: impl Into<String>, check: F) -> Self {
    Self {
      name: name.into(),
      check,
      _marker: std::marker::PhantomData,
    }
  }
}

impl<I, O, F> Oracle<I, O> for FnOracle<I, O, F>
where
  F: Fn(I, &OracleCtx) -> OracleResult<O>,
{
  fn name(&self) -> &str {
    &self.name
  }

  fn check(&self, input: I, ctx: &OracleCtx) -> OracleResult<O> {
    (self.check)(input, ctx)
  }
}

pub fn define_oracle<I, O, F>(name: impl Into<String>, check: F) -> FnOracle<I, O, F>
where
  F: Fn(I, &OracleCtx) -> OracleResult<O>,
{
  FnOracle::new(name, check)
}

