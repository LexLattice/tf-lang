pub mod canonical;
pub mod context;
pub mod oracle;
pub mod result;

pub use canonical::{
  canonical_bytes,
  canonical_string,
  canonicalize,
  canonicalize_value,
};
pub use context::{
  create_ctx,
  derive_ctx,
  OracleCtx,
  OracleCtxBuilder,
  OracleCtxError,
};
pub use oracle::{define_oracle, FnOracle, Oracle};
pub use result::{
  error,
  error_with_details,
  err,
  failure,
  failure_result,
  format_failure,
  from_error,
  is_ok,
  map_value,
  merge_warnings,
  ok,
  ok_with_warnings,
  OracleError,
  OracleFailure,
  OracleOk,
  OracleResult,
};

#[cfg(test)]
mod tests {
  use super::*;
  use pretty_assertions::assert_eq;
  use serde_json::json;

  #[test]
  fn canonicalizes_objects() {
    let value = json!({"b":2,"a":1});
    let canon = canonicalize_value(&value);
    assert_eq!(canon, json!({"a":1,"b":2}));
  }

  #[test]
  fn ok_merges_warnings() {
    let ok = ok_with_warnings(1, ["a", "b", "a"]);
    match ok {
      OracleResult::Ok(result) => {
        assert_eq!(result.warnings, vec!["a", "b"]);
      }
      _ => panic!("expected ok"),
    }
  }
}

