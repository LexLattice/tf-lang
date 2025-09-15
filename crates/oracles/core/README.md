# tf-oracles-core

Rust mirror of the TF-Lang oracle contracts. Provides shared result types, canonical JSON helpers, and a minimal context used by all Rust oracles.

## Contracts

- `OracleCtx` — captures `{ seed: String, now: i64 }` and exposes `canonicalize`/`canonical_json_string` helpers.
- `OracleOutcome<T>` — enum compatible with the JSON tagged union `{ ok: true, value, warnings? } | { ok: false, error, trace? }`.
- `Oracle<I, O>` — trait with a single method `check(&self, input: I, ctx: &OracleCtx) -> OracleOutcome<O>`.
- Helper constructors `ok`, `ok_with_warnings`, and `err` mirror the TypeScript helpers.

## Usage

```rust
use tf_oracles_core::{ok, err, OracleCtx, ErrorOptions};

let ctx = OracleCtx::new("0xfeed", 0);
let canonical = ctx.canonicalize(&serde_json::json!({"balance": 42.125}))?;
let result = ok(canonical);
```

## Tests

Run the workspace tests:

```bash
cargo test --workspace --all-targets
```

## Failure anatomy

Example error payload:

```json
{
  "ok": false,
  "error": {
    "code": "E_CONSERVATION_LEAK",
    "explain": "asset totals diverged",
    "details": { "leak": 3 }
  },
  "trace": ["before-apply", "after-apply"]
}
```

Ensure `details` are canonicalized before returning to keep parity with the TypeScript runtime.
