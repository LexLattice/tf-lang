use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::canonical::{canonicalize, canonicalize_value, CanonError};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OracleCtx {
    pub seed: String,
    pub now: i64,
}

impl OracleCtx {
    pub fn new(seed: impl Into<String>) -> Self {
        Self {
            seed: seed.into(),
            now: 0,
        }
    }

    pub fn with_now(mut self, now: i64) -> Self {
        self.now = now;
        self
    }

    pub fn seed(&self) -> &str {
        &self.seed
    }

    pub fn now(&self) -> i64 {
        self.now
    }

    pub fn canonicalize<T>(&self, value: &T) -> Result<Value, CanonError>
    where
        T: Serialize,
    {
        canonicalize(value)
    }

    pub fn canonicalize_value(&self, value: Value) -> Value {
        canonicalize_value(value)
    }
}
