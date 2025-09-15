# tf-oracles-determinism

Rust implementation of the determinism oracle shared with the TS runtime.

## Overview

- Validates that every run for a case `{name, seed}` ends with the same
  canonical `final` snapshot and identical checkpoint map.
- Uses `tf-oracles-core` for canonicalization and result formatting.
- Reports `E_NON_DETERMINISTIC` with structured evidence per mismatching run.

## Usage

```rust
use std::collections::BTreeMap;

use serde_json::json;
use tf_oracles_core::{OracleCtx, OracleResult};
use tf_oracles_determinism::{check_determinism, DeterminismCase, DeterminismInput, DeterminismRun};

fn main() {
    let runs = vec![
        DeterminismRun {
            run_id: "baseline".into(),
            final_state: json!({"p": 100}),
            checkpoints: BTreeMap::new(),
            note: None,
        },
        DeterminismRun {
            run_id: "rerun".into(),
            final_state: json!({"p": 100}),
            checkpoints: BTreeMap::new(),
            note: None,
        },
    ];

    let input = DeterminismInput {
        cases: vec![DeterminismCase {
            name: "price-feed".into(),
            seed: "0x01".into(),
            runs,
        }],
    };

    let ctx = OracleCtx::new("0xfeed").with_now(0);
    match check_determinism(&input, &ctx) {
        OracleResult::Success(report) => println!("runs checked: {}", report.value.runs_checked),
        OracleResult::Failure(failure) => panic!("unexpected drift: {}", failure.error.code),
    }
}
```

## Tests

```bash
cargo test --manifest-path crates/Cargo.toml -p tf-oracles-determinism
```

Rust property seeds mirror the TS seeds and live in
`tests/seeds.json`.

Fixtures shared with the TS runtime are stored in
`packages/oracles/determinism/fixtures/` and the tests exercise each JSON case
directly.

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
