# tf-oracles-determinism

Rust implementation of the determinism oracle shared with the TS runtime.

## Overview

- Validates that every run for a case `{name, seed}` ends with the same
  canonical `final` snapshot and identical checkpoint map.
- Uses `tf-oracles-core` for canonicalization and result formatting.
- Reports `E_NON_DETERMINISTIC` with structured evidence per mismatching run.

## Usage

```rust
use tf_oracles_core::OracleCtx;
use tf_oracles_determinism::{check_determinism, DeterminismCase, DeterminismInput, DeterminismRun};

let input = DeterminismInput {
    cases: vec![DeterminismCase {
        name: "price-feed".into(),
        seed: "0x01".into(),
        runs: vec![
            DeterminismRun { run_id: "baseline".into(), final_state: serde_json::json!({"p": 100}), checkpoints: Default::default(), note: None },
            DeterminismRun { run_id: "rerun".into(), final_state: serde_json::json!({"p": 100}), checkpoints: Default::default(), note: None },
        ],
    }],
};
let ctx = OracleCtx::new("0xfeed").with_now(0);
let result = check_determinism(&input, &ctx);
```

## Tests

```bash
cargo test --manifest-path crates/Cargo.toml -p tf-oracles-determinism
```

Rust property seeds mirror the TS seeds and live in
`tests/seeds.json`.

## Failure anatomy

On drift the oracle returns:

```json
{
  "ok": false,
  "error": {
    "code": "E_NON_DETERMINISTIC",
    "explain": "Runs diverged under identical seeds",
    "details": {
      "mismatches": [
        {
          "case": "price-feed",
          "seed": "0xfeed1",
          "run": "rerun",
          "mismatches": [
            {
              "checkpoint": "final",
              "expected": {"balances": {"USD": 1000, "BTC": 1}},
              "actual": {"balances": {"USD": 1000, "BTC": 1.0005}}
            }
          ]
        }
      ]
    }
  }
}
```

The structure matches the TypeScript oracle so fixtures are interchangeable.
