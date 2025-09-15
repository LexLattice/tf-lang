# @tf/oracles-core

Common contracts used by all oracles.

- **Oracle<I,O>**: `check(input: I, ctx: OracleCtx) -> Promise<Result<O,OracleError>>`
- **OracleCtx**: `{ seed: string; now: number; canonicalize(x): any }`
- **Result<T,E>**:
  - OK: `{ ok: true, value: T, warnings?: string[] }`
  - ERR: `{ ok: false, error: { code: string, explain: string, details?: any }, trace?: string[] }`

**Principles:** deterministic, side‑effect free, offline. All returned structures are JSON‑serializable and stable. Each oracle has a tiny README + fixtures/docs living next to code.
