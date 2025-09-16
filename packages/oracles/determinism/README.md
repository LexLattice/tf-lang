# @tf/oracles-determinism

Oracle that verifies replaying a scenario with the same seed yields identical
checkpoints and final state.

## Overview

- Accepts `{ cases: [{ name, seed, runs: [{ runId, final, checkpoints }] }] }`.
- Canonicalises each run via `@tf/oracles-core` before comparing.
- Emits `E_NON_DETERMINISTIC` when any checkpoint or final snapshot diverges.

## Usage

```ts
import { createDeterminismOracle } from "@tf/oracles-determinism";
import { createOracleCtx } from "@tf/oracles-core";

const oracle = createDeterminismOracle();
const ctx = createOracleCtx("0xfeed", { now: 0 });
const result = await oracle.check({
  cases: [
    {
      name: "price-feed",
      seed: "0x01",
      runs: [
        { runId: "baseline", final: { balances: { USD: 1000 } }, checkpoints: {} },
        { runId: "rerun", final: { balances: { USD: 1000 } }, checkpoints: {} }
      ],
    },
  ],
}, ctx);
```

## Tests

```bash
pnpm -C packages/oracles/determinism build
pnpm -C packages/oracles/determinism test
```

Property seeds live in `tests/seeds.json` (TS) and `crates/oracles/determinism/tests/seeds.json`
for the Rust crate.

## Failure anatomy

Regression fixtures live under `packages/oracles/determinism/fixtures`. Each
fixture records the oracle input and the expected outcome. For example
`non-deterministic.json` captures a drifted price feed rerun:

```json
{
  "input": {
    "cases": [
      {
        "name": "price-feed",
        "seed": "0xfeed1",
        "runs": [
          {
            "runId": "initial",
            "final": { "balances": { "USD": 1000, "BTC": 1 } },
            "checkpoints": {
              "pre": { "balances": { "USD": 1000, "BTC": 1 } },
              "post": { "balances": { "USD": 990, "BTC": 1.01 } }
            }
          },
          {
            "runId": "rerun",
            "final": { "balances": { "USD": 1000, "BTC": 1.0005 } },
            "checkpoints": {
              "pre": { "balances": { "USD": 1000, "BTC": 1 } },
              "post": { "balances": { "USD": 989, "BTC": 1.015 } }
            }
          }
        ]
      }
    ]
  },
  "expect": {
    "ok": false,
    "mismatches": [
      {
        "case": "price-feed",
        "seed": "0xfeed1",
        "run": "rerun",
        "checkpoints": ["final", "post"]
      }
    ]
  }
}
```

Feeding the `input` into the oracle returns a failure with the mismatches above
and a trace of the first drifting runs. The TS and Rust tests load these JSON
fixtures directly, ensuring both runtimes stay in sync.
