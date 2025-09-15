use std::sync::Arc;

use serde::Serialize;
use serde_json::Value;

use crate::canonical::{canonicalize, canonicalize_value};

pub type CanonicalFn = Arc<dyn Fn(&Value) -> Value + Send + Sync + 'static>;

#[derive(Clone)]
pub struct OracleCtx {
  seed: String,
  now: i64,
  canonicalize: CanonicalFn,
}

impl OracleCtx {
  pub fn seed(&self) -> &str {
    &self.seed
  }

  pub fn now(&self) -> i64 {
    self.now
  }

  pub fn canonicalize_value(&self, value: &Value) -> Value {
    (self.canonicalize)(value)
  }

  pub fn canonicalize<T>(&self, value: &T) -> Result<Value, serde_json::Error>
  where
    T: Serialize,
  {
    canonicalize(value)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleCtxError {
  EmptySeed,
}

pub struct OracleCtxBuilder {
  seed: String,
  now: i64,
  canonicalize: Option<CanonicalFn>,
}

impl OracleCtxBuilder {
  pub fn new(seed: impl Into<String>, now: i64) -> Self {
    Self {
      seed: seed.into(),
      now,
      canonicalize: None,
    }
  }

  pub fn with_canonicalize(mut self, canonicalize: CanonicalFn) -> Self {
    self.canonicalize = Some(canonicalize);
    self
  }

  pub fn build(self) -> Result<OracleCtx, OracleCtxError> {
    if self.seed.trim().is_empty() {
      return Err(OracleCtxError::EmptySeed);
    }
    let canonicalize = self
      .canonicalize
      .unwrap_or_else(|| Arc::new(|value: &Value| canonicalize_value(value)));
    Ok(OracleCtx {
      seed: self.seed,
      now: self.now,
      canonicalize,
    })
  }
}

pub fn create_ctx(seed: impl Into<String>, now: i64) -> Result<OracleCtx, OracleCtxError> {
  OracleCtxBuilder::new(seed, now).build()
}

pub fn derive_ctx(base: &OracleCtx, now: Option<i64>, seed: Option<String>) -> OracleCtx {
  OracleCtx {
    seed: seed.unwrap_or_else(|| base.seed.clone()),
    now: now.unwrap_or_else(|| base.now),
    canonicalize: Arc::clone(&base.canonicalize),
  }
}

