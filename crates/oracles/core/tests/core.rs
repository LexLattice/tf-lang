use pretty_assertions::assert_eq;
use proptest::prelude::*;
use proptest::strategy::Strategy;
use serde_json::{json, Map, Number, Value};
use tf_oracles_core::canonical::canonicalize_value;
use tf_oracles_core::context::{create_ctx, derive_ctx, OracleCtxBuilder, OracleCtxError};
use tf_oracles_core::oracle::define_oracle;
use tf_oracles_core::result::{
  failure,
  format_failure,
  is_ok,
  map_value,
  merge_warnings,
  ok,
  ok_with_warnings,
};
use tf_oracles_core::{canonical_bytes, canonical_string, Oracle};

#[test]
fn create_ctx_validates_seed() {
  let result = OracleCtxBuilder::new("", 0).build();
  assert!(matches!(result, Err(OracleCtxError::EmptySeed)));
}

#[test]
fn canonicalize_stable() {
  let value = json!({"b":2,"a":{"y":1,"x":2}});
  let first = canonicalize_value(&value);
  let second = canonicalize_value(&first);
  assert_eq!(first, second);
  assert_eq!(canonical_string(&value).unwrap(), canonical_string(&first).unwrap());
  assert_eq!(canonical_bytes(&value).unwrap(), canonical_bytes(&first).unwrap());
}

#[test]
fn ctx_canonicalizes() {
  let ctx = create_ctx("seed", 0).unwrap();
  let canon = ctx.canonicalize(&json!({"b":1,"a":2})).unwrap();
  assert_eq!(canon, json!({"a":2,"b":1}));
  let derived = derive_ctx(&ctx, Some(10), None);
  assert_eq!(derived.now(), 10);
  assert_eq!(derived.seed(), "seed");
}

#[test]
fn results_helpers() {
  let ok_result = ok_with_warnings(1, ["b", "a"]);
  let merged = match ok_result {
    tf_oracles_core::OracleResult::Ok(result) => merge_warnings(result, ["c", "a"]),
    _ => panic!("expected ok"),
  };
  assert_eq!(merged.warnings, vec!["a", "b", "c"]);

  let err = failure("E", "boom", Some(json!({"b":2,"a":1})), ["z", "a"]);
  assert_eq!(
    err.trace,
    vec!["a", "z"],
  );
  assert_eq!(
    err.error.details,
    Some(json!({"a":1,"b":2})),
  );

  let mapped = map_value(ok(10), |value| value + 1);
  match mapped {
    tf_oracles_core::OracleResult::Ok(result) => assert_eq!(result.value, 11),
    _ => panic!("expected ok"),
  }

  let formatted = format_failure(&tf_oracles_core::OracleResult::Err(err));
  assert!(formatted.unwrap().starts_with("E: boom"));
}

#[test]
fn oracle_wrapper_runs() {
  let oracle = define_oracle("add-one", |input: i32, _ctx| ok(input + 1));
  let ctx = create_ctx("seed", 0).unwrap();
  let result = oracle.check(3, &ctx);
  assert!(is_ok(&result));
}

proptest! {
  #[test]
  fn canonicalization_idempotent(value in json_strategy()) {
    let first = canonicalize_value(&value);
    let second = canonicalize_value(&first);
    prop_assert_eq!(first, second);
  }
}

fn json_strategy() -> impl Strategy<Value = Value> {
  let leaf = prop_oneof![
    Just(Value::Null),
    any::<bool>().prop_map(Value::Bool),
    any::<i64>().prop_map(|n| Value::Number(Number::from(n))),
    any::<f64>().prop_map(|f| Number::from_f64(f).map(Value::Number).unwrap_or(Value::Null)),
    proptest::string::string_regex(".{0,8}").unwrap().prop_map(Value::String),
  ];

  leaf.prop_recursive(3, 32, 6, |inner| {
    prop_oneof![
      proptest::collection::vec(inner.clone(), 0..4).prop_map(Value::Array),
      proptest::collection::vec((proptest::string::string_regex(".{1,8}").unwrap(), inner), 0..4)
        .prop_map(|entries| {
          let mut map = Map::new();
          for (k, v) in entries {
            map.insert(k, v);
          }
          Value::Object(map)
        }),
    ]
  })
}

