# @tf/oracles-core

Shared contracts, helpers, and canonical JSON utilities consumed by all TF-Lang oracles.

## Contracts

- **`Oracle<I, O>`** — function taking an input payload and an `OracleCtx`, returning an `OracleOutcome<O>` or a promise thereof.
- **`OracleCtx`** — `{ seed: string; now: number; canonicalize(value) }`. Tests fix `now` and feed deterministic seeds.
- **`OracleOutcome<T>`** — tagged union with `{ ok: true, value, warnings? }` or `{ ok: false, error, trace? }`.

Helper exports:

- `ok(value, warnings?)` / `err(code, explain, { details?, trace? })`
- `canonicalize(value)` → recursively sorted, float-stabilised structure
- `canonicalJSONString(value)` → canonical JSON string suitable for hashing/logging
- `createCtx(seed, now)` → minimal context with default canonicalizer

## Usage

```ts
import { createCtx, ok, err, canonicalize } from "@tf/oracles-core";

const ctx = createCtx("0xfeed", 0);
const result = ok(ctx.canonicalize({ balance: 42.125 }));
```

## Tests

- `pnpm -w build`
- `pnpm -w test`

Vitest suites live in `packages/oracles/core/tests` and remain deterministic.

## Failure anatomy

Errors follow the schema `{ ok: false, error: { code, explain, details? }, trace? }`. For example:

```json
{
  "ok": false,
  "error": {
    "code": "E_CHECKPOINT_MISMATCH",
    "explain": "final state diverged",
    "details": { "diff": "…" }
  },
  "trace": ["checkpoint-1", "checkpoint-2"]
}
```

Always canonicalize `details` before returning so diffs remain stable across runtimes.
