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

Property seeds are recorded in `tests/seeds.json` (TS) and mirrored in the Rust
crate.

## Failure anatomy

Given `fixtures/non-deterministic.json`:

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
            {"checkpoint": "final"},
            {"checkpoint": "post"}
          ]
        }
      ]
    }
  },
  "trace": ["case:price-feed:run:rerun"]
}
```

The oracle highlights every checkpoint that deviated, allowing CI to surface
the exact drift.
