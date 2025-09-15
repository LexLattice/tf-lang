# @tf/oracles-determinism

Determinism oracle validating that identical seeds yield identical checkpoints and final states across runtimes.

## Overview

- Input: `{ runs: [{ runtime, checkpoints: [{ label, state }], finalState }] }`
- Requirement: every runtime must emit checkpoints with the same labels and canonicalized states, ending in the same final state.
- Output: success report `{ seed, runs: [{ runtime, checkpoints }] }` or an error pointing to the divergent path.

## Usage

```ts
import { determinismOracle } from "@tf/oracles-determinism";
import { createCtx } from "@tf/oracles-core";

const ctx = createCtx("0x6f2a7c9bbabc1234", 0);
const result = determinismOracle({
  runs: [
    { runtime: "ts", checkpoints: [], finalState: { value: 1 } },
    { runtime: "rs", checkpoints: [], finalState: { value: 1 } }
  ],
}, ctx);
```

## Tests

- `pnpm --filter @tf/oracles-determinism build`
- `pnpm --filter @tf/oracles-determinism test`

Property tests use fixed seeds (`0x6f2a7c9b`, `0x5eadbeef`) to stay deterministic.

## Failure anatomy

Example error for a mismatched final state (`fixtures/final-mismatch.json`):

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

## Fixtures

- `fixtures/happy.json` – matching checkpoints/finals (should pass)
- `fixtures/final-mismatch.json` – mismatched final value (should fail)
- `fixtures/label-mismatch.json` – mismatched checkpoint label (should fail)
