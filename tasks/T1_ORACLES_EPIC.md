# T1_ORACLES_EPIC — Oracles, Harness, Strength (TS + Rust)

Covers: T1_2 Oracle Stdlib, T1_3 Determinism Oracle, T1_4 Conservation Oracle, T1_5 Idempotence Oracle, T1_6 Transport/Region Oracle (+ visualizer), T1_7 Conservativity Oracle (+ call-graph tool), T1_8 Oracle Harness (PBT), T1_9 Oracle Strength (Mutation Testing). Starts from T1_1 schema (already complete).

## ACCEPTANCE

### Evidence (rollup)
- TS & Rust packages:
  - `packages/oracles/core` and `crates/oracles/core` (interfaces, result types)
  - `packages/oracles/{determinism,conservation,idempotence,transport,conservativity}`
  - `crates/oracles/{determinism,conservation,idempotence,transport,conservativity}`
- Harness + mutation:
  - `packages/harness/pbt`, `crates/harness/pbt` (reproducible seeds + shrinkers)
  - `packages/mutation`, `crates/mutation` (targeted mutants + matrix)
- Visuals & tools:
  - Region visualizer (static HTML/SVG) under `packages/oracles/transport/visualizer/`
  - CALL gate call-graph tool: `packages/oracles/conservativity/tools/callgraph.ts` and Rust equivalent if implemented
- Docs:
  - README in each package; brief explainers for failure outputs; seed rule doc at `docs/harness/seeds.md`
- Reports & artifacts:
  - `out/t1/oracles-report.json` (all oracle outcomes on fixtures)
  - `out/t1/mutation-matrix.json` (which oracle caught which mutant)
  - `out/t1/coverage.html` (static HTML rollup)
  - `out/t1/harness-seeds.jsonl` (emitted seeds per failing run)

### CI
- Jobs (names are authoritative):
  - **`oracle-core`** — build core libs (TS+Rust), unit tests pass.
  - **`determinism-oracle`** — property tests + a couple of mutation probes.
  - **`conservation-oracle`** — fixtures exercise asset/balance conservation; produces clear diffs on leakage/orphans.
  - **`idempotence-oracle`** — randomized property tests, double-apply effects → same state.
  - **`transport-region-oracle`** — tests for region boundaries; exports the static region visualizer artifact.
  - **`conservativity-oracle`** — tests that CALL gates only emit declared effects; call-graph tool runs on TS sources and emits a JSON graph.
  - **`oracle-harness`** — runs PBT harness in both runtimes, time-budgeted; seeds recorded.
  - **`oracle-strength`** — runs mutation suite, emits matrix; **fails if kill-rate < 80%**.
- Each job:
  - runs in both TS and Rust where applicable (matrix)
  - is offline, deterministic, and uploads its artifacts under `out/t1/…`

### Determinism
- Canonical JSON for any serialized result; re-run determinism assertions twice; record seeds and keys used; forbid system time/env in tests (mock `now`).

### Docs
- Each package has: overview (1–2 paragraphs), how to run tests, and a “failure anatomy” section (example JSON + human explanation).

### Parity
- Where both runtimes exist: structural parity on fixtures and at least N=3 seeded cases (expect identical checkpoints or justified diffs).

### Metrics (minimums)
- Mutation kill‑rate ≥ **80%** (targeted mutants).
- Harness runtime per CI job ≤ **5 minutes** (per card T1_8).

## BLOCKERS (policy & rules)
- `schema_changes_allowed: false` (uses T1_1 schema)
- Must not: cross-test state, nondeterminism, introduce runtime deps (CI dev deps ok), tracing overhead when `DEV_PROOFS=0`, change APIs/file formats beyond this epic’s scope, or gate merges on local hooks.
- Machine rules: TS (`no_deep_imports`, `internal_esm_imports_end_with_js`, `no_as_any`), Rust (`no_static_mut`, `no_panicking_unwraps_in_libs`, `use_atomics_mutexes_appropriately`), Runtime deps `{allowed:false, ci_dev_deps_allowed:true}`.

## END_GOAL (workplan)
1) **Oracle Stdlib (T1_2)**: establish `Oracle<I,O>`, `OracleCtx`, `Result` in TS/Rust; stub a few helpers (JSON explainers).
2) **Determinism Oracle (T1_3)**: assert identical final state & checkpoints for same seed; property + light mutation tests.
3) **Conservation Oracle (T1_4)**: detect asset/balance leakage; crisp diff report on fixture violations.
4) **Idempotence Oracle (T1_5)**: double‑apply effects → no change after first apply; randomized tests with seeds.
5) **Transport/Region Oracle (T1_6)**: ensure lenses respect declared regions; ship static region visualizer artifact.
6) **Conservativity Oracle (T1_7)**: CALL gate emits only declared effects; provide TS call‑graph JSON tool (Rust optional).
7) **Oracle Harness (T1_8)**: property-based harness in TS/Rust with reproducible seeds and shrinkers; per‑failure emit minimal seed corpus.
8) **Oracle Strength (T1_9)**: mutation scripts against minimal crypto‑bot models; produce coverage matrix + kill‑rate ≥80%.
9) Roll‑up report & single HTML: generate `coverage.html` and `oracles-report.json`, attach in CI artifacts.

## EVIDENCE INDEX (paths)
- Core: `packages/oracles/core`, `crates/oracles/core`
- Oracles: `packages/oracles/*`, `crates/oracles/*`
- Harness: `packages/harness/pbt`, `crates/harness/pbt`; Seeds doc at `docs/harness/seeds.md`
- Mutation: `packages/mutation`, `crates/mutation`
- Visuals: `packages/oracles/transport/visualizer/`
- Tools: `packages/oracles/conservativity/tools/callgraph.ts`
