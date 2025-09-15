# tf-oracles-core

Rust mirror of the oracle stdlib. Provides:

- `Oracle<I, O>` trait and `define_oracle` helper for pure, deterministic checks.
- `OracleCtx` builder with canonical JSON support (shared with TS via schema).
- Result helpers (`ok`, `failure`, `merge_warnings`) emitting serde-friendly structs.
- Canonical JSON utilities (`canonicalize_value`, `canonical_string`, `canonical_bytes`).

The crate is `no_std`? no (uses `std`), but free of external runtime deps beyond
`serde`/`serde_json`. Every function avoids panicking unwraps and returns
`Result` where serialization may fail.

## Usage

```rust
use serde_json::json;
use tf_oracles_core::{
    create_ctx,
    define_oracle,
    failure_result,
    ok,
    OracleResult,
};

let oracle = define_oracle("checksum", |input: serde_json::Value, ctx| {
    let canonical = match ctx.canonicalize(&input) {
        Ok(value) => value,
        Err(err) => {
            return failure_result(
                "E_CANON",
                "failed to canonicalize",
                Some(json!({"error": err.to_string()})),
                ["checksum"],
            );
        }
    };
    if canonical == serde_json::Value::Null {
        return failure_result("E_EMPTY", "payload missing", None, ["checksum"]);
    }
    ok(canonical)
});

let ctx = create_ctx("seed", 1).unwrap();
let result: OracleResult<_> = oracle.check(json!({"a": 1}), &ctx);
```

## Testing

```bash
cargo test -p tf-oracles-core
```

## Failure anatomy

```json
{
  "ok": false,
  "error": {
    "code": "E_EMPTY",
    "explain": "payload missing"
  },
  "trace": ["checksum"]
}
```

Traces are sorted and de-duplicated; details are canonicalized before serialization.
