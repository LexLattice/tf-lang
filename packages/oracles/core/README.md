# @tf/oracles-core

Deterministic primitives shared by every oracle implementation. The package exposes:

- **`Oracle<I, O>`** — asynchronous contract returning a tagged `OracleResult<O>`.
- **`OracleCtx`** — seed, fixed `now`, and canonicalization helper for stable JSON.
- **Result helpers** — `ok`, `failure`, `mergeWarnings`, `formatFailure`, etc.
- **Canonical JSON tools** — `canonicalize`, `canonicalStringify`, `canonicalBuffer`.

All helpers are side-effect free and avoid runtime dependencies. The canonicalization
rules match the Rust implementation (sorted object keys, deterministic sets/maps,
`NaN` → `null`).

## Usage

```ts
import {
  createOracleCtx,
  defineOracle,
  failure,
  ok,
} from "@tf/oracles-core";

const checksumOracle = defineOracle("checksum", (input: { payload: string }) => {
  if (input.payload.length === 0) {
    return failure("E_EMPTY", "payload must be non-empty");
  }
  const hash = [...input.payload].reduce((acc, ch) => acc + ch.charCodeAt(0), 0);
  return ok({ hash });
});

const ctx = createOracleCtx({ seed: "seed-1", now: 1_700_000_000 });
const result = await checksumOracle.check({ payload: "tf" }, ctx);
```

## Testing

Run the vitest suite (deterministic, no network or timers):

```bash
pnpm --filter @tf/oracles-core build
pnpm --filter @tf/oracles-core test
```

## Failure anatomy

Every failure is canonical JSON:

```json
{
  "ok": false,
  "error": {
    "code": "E_EMPTY",
    "explain": "payload must be non-empty"
  },
  "trace": ["checksum"]
}
```

Trace entries are de-duplicated and sorted to keep reports deterministic.
