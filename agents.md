# Agents — T1 Oracles Epic (TS + Rust)

**Mission:** Implement and wire up the remaining T1 tasks (T1_2…T1_9) in `tf-lang`, starting from the T1_1 schema (PR #106). Ship minimal-but-real implementations with deterministic tests, a shared oracle interface, a property-based harness, and mutation coverage.

**North-star “green” checks (must pass in CI):**
- `oracle-core`, `determinism-oracle`, `conservation-oracle`, `idempotence-oracle`,
  `transport-region-oracle`, `conservativity-oracle`, `oracle-harness`, `oracle-strength`.

**Repository working lanes (TS and Rust):**
- TS: `packages/oracles/*`, `packages/harness/pbt`, `packages/mutation`
- Rust: `crates/oracles/*`, `crates/harness/pbt`, `crates/mutation`
- Docs live beside sources (`README.md`, small diagrams, example fixtures).

**Global policy (do not violate):**
- Must not: cross-test state, nondeterminism, runtime deps (CI‑only dev deps allowed), or file/format drift beyond the task scope; don’t gate merges on local hooks; use canonical JSON where applicable; TS→ no deep imports, add “.js” to internal ESM, no `as any`; Rust→ no `static mut`, no panicking unwraps in libs.  
  _If you must override a rule, record `{reason, owner, expiry}` in `overrides.json` at task scope and keep it local._ 

**Determinism & parity:**
- Use canonical JSON encoders; re-run determinism assertions twice; capture seeds; where both runtimes exist, aim for structural parity. Keep tests offline and repeatable.

**Interfaces (authoritative, keep stable):**
- `Oracle<I,O>`: `check(input: I, ctx: OracleCtx) -> Result<O, OracleError>`  
- `OracleCtx`: `{ seed: string, now: number, canonicalize: (x:any)=>any }`  
- `Result`: tagged union `{ ok:true,value:T,warnings? } | { ok:false,error:{code,explain,details?}, trace? }`  
- Rust: mirror the shape via structs/serde for JSON compatibility.

**Tooling & deps constraints:**
- TS dev deps allowed (examples): `fast-check`, `typescript`, `ts-node`, `ajv` for schema validation where needed.
- Rust dev deps allowed (examples): `proptest`, `serde`, `serde_json`. Avoid new runtime deps.
- No network in tests; fixtures must be local; long fuzz phases respect a local time budget.

**Operational contract during the run:**
- Work on branch `feature/t1-oracles-epic`.
- Keep a timestamped build log at `AGENT_LOG.md` (append-only). After each milestone, run tests and commit with a short body including seed(s) used.
- If blocked, write a single paragraph to `TODO.md` (what, why, next attempt). Prefer smallest working subset over breadth.

**Definition of done:**
- All green checks listed above.
- `oracle-harness` seeds are reproducible across TS/Rust on at least 5 tricky cases (float/time/I/O avoided).
- `oracle-strength` mutation kill-rate ≥80% on the targeted mutants.
- Each oracle has: interface contract + tests + a tiny README + one JSON/Markdown example.

**Artifacts to upload (CI):**
- `out/t1/oracles-report.json` (rollup), `out/t1/harness-seeds.jsonl`, `out/t1/mutation-matrix.json`, `out/t1/coverage.html`.
