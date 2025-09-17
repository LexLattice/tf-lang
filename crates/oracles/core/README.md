# tf-oracles-core

Rust primitives shared by the TF oracle implementations.

## Overview

- `OracleCtx` stores `{ seed, now }` and offers `canonicalize` helpers.
- `OracleResult<T>` mirrors the JSON surface `{ ok, value? | error }`.
- Constructors `ok`, `err`, `err_with_details`, and `with_trace` keep payloads
  normalized (trimmed text, deduped warnings/trace).
- Canonicalizers (`canonicalize`, `canonical_json`, `pretty_canonical_json`,
  `deep_equal`) deep-clone values, alphabetise object keys, round floats to 12
  decimals, and expose JSON pointer helpers for first-diff reporting.

## Usage

```rust
use serde_json::json;
use tf_oracles_core::{ok, OracleCtx, OracleResult};

fn main() -> Result<(), tf_oracles_core::CanonicalizeError> {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let canonical = ctx.canonicalize(&json!({"foo": 1}))?;
    let result = ok(canonical, []);
    assert!(matches!(result, OracleResult::Success(_)));
    Ok(())
}
```

## Tests

```bash
cargo test --manifest-path crates/Cargo.toml -p tf-oracles-core
```

## Failure anatomy

```json
{
  "ok": false,
  "error": {
    "code": "E_STATE_DRIFT",
    "explain": "Final snapshot diverged from expected canonical form",
    "details": {
      "expected": {"count": 2},
      "actual": {"count": 3}
    }
  },
  "trace": ["snapshot:final"]
}
```

The structure matches the TypeScript runtime, ensuring fixtures and harnesses
can diff failures across runtimes without glue code.
