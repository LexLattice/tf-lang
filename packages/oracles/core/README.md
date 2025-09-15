# @tf/oracles-core

Shared contracts for TF oracles in TypeScript.

## Overview

The core module exposes:

- `Oracle<I, O>` – a pure checker returning a deterministic `OracleResult<O>`.
- `OracleCtx` – execution context `{ seed, now, canonicalize }`.
- Helpers `ok`, `err`, and `withTrace` for shaping success/failure payloads.
- `defaultCanonicalize` / `canonicalStringify` for canonical JSON output.
- `createOracleCtx(seed, init?)` for building contexts in tests and fixtures.

All values passed through `canonicalize` are deeply cloned, object keys are
sorted, floats are rounded to 12 decimals, and unsupported data (e.g. `bigint`)
are stringified. This keeps diagnostics stable across TS/Rust runtimes.

## Usage

```ts
import { createOracleCtx, ok, err } from "@tf/oracles-core";

const ctx = createOracleCtx("0xfeed", { now: 0 });
const result = ok({ final: ctx.canonicalize({ foo: 1 }) });
```

## Tests

```bash
pnpm -C packages/oracles/core build
pnpm -C packages/oracles/core test
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

Errors always use uppercase codes, trimmed explanations, and optional structured
`details` to aid diffing in the oracle harness.
