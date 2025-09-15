# tf-oracles-determinism

Rust determinism oracle mirroring the TypeScript implementation. Ensures that identical seeds yield identical checkpoint streams and final states across runtimes.

## API

```rust
use tf_oracles_core::OracleCtx;
use tf_oracles_determinism::{check, DeterminismInput};

let ctx = OracleCtx::new("0x6f2a7c9bbabc1234", 0);
let input = DeterminismInput {
    runs: vec![
        DeterminismRun {
            runtime: "ts".into(),
            checkpoints: vec![],
            final_state: serde_json::json!({ "value": 1 }),
        },
        DeterminismRun {
            runtime: "rs".into(),
            checkpoints: vec![],
            final_state: serde_json::json!({ "value": 1 }),
        },
    ],
};
let outcome = check(input, &ctx);
```

The oracle returns `OracleOutcome<DeterminismReport>` describing the compared runs or an error with a canonical diff.

## Tests

```bash
cargo test --package tf-oracles-determinism
```

Property tests use fixed RNG seeds (`0x6f2a7c9bbabc1234`, `0x5eadbeefcafebabe`) for reproducibility.

## Failure anatomy

For `fixtures/final-mismatch.json`:

```json
{
  "ok": false,
  "error": {
    "code": "E_DETERMINISM_FINAL_STATE",
    "explain": "final state diverged",
    "details": {
      "diff": {
        "path": "/",
        "left": { "balance": 15 },
        "right": { "balance": 17 }
      }
    }
  },
  "trace": ["ts", "rs"]
}
```

Fixtures live next to the TypeScript package for parity with cross-runtime tests.
