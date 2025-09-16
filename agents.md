# Agents — T3 Oracles Epic (Conservation • Idempotence • Transport)

**Mission:** Implement the next three cross‑runtime oracles and wire them into CI with deterministic, canonical artifacts:
- **T3_1 — Conservation** (TS + Rust)
- **T3_2 — Idempotence** (TS + Rust)
- **T3_3 — Transport (serialize/round‑trip)** (TS + Rust)
- **T3_4 — Parity & Contract Tests** (TS↔Rust parity for each oracle)
- **T3_5 — CI & Docs** (jobs, artifacts, PR reporting)

You will build small packages/crates under the existing oracles core (reuse T1/T2 core types).

## Rails (must NOT violate)
- Deterministic: stable key order; canonical JSON; fixed `now` in tests; repeat determinism **2×**.
- **No runtime deps** (devDeps OK for building/testing, e.g., vitest/tsx/clap in Rust **bin only**).
- TS: ESM with internal imports ending in **`.js`**; no deep imports across packages; no `as any`.
- Rust: no `static mut`; no panicking `unwrap()`/`expect()` in libraries; prefer `Result`; use `BTree*` for ordering.
- Use shared helpers from **`@tf-lang/utils`** (canonical JSON, findRepoRoot, tmp handling, HTML escape). Do **not** duplicate these utilities.
- Tests must be self‑contained and offline; no network; reproducible seeds checked in.

## ABI (stable from T1 core)
- TS: `Oracle<I,O>(input, ctx) -> Promise<OracleResult>` and helpers from `@tf-lang/oracles-core-ts`.
- Rust: analogous traits/types from `tf-oracles-core`.
- **Do not change** the public ABI of the core libraries; implement new oracles as add‑on packages/crates.

## Artifacts (required for CI green)
- **Conservation:** `out/t3/conservation/report.json`
- **Idempotence:** `out/t3/idempotence/report.json`
- **Transport:** `out/t3/transport/report.json`
- **Parity:** `out/t3/parity/{conservation,idempotence,transport}.json` with `{ "equal": true, ... }`

All artifacts must be canonical JSON with trailing newline.

## Folder targets (create if missing)
- TS: `packages/oracles/{conservation,idempotence,transport}/`
- Rust: `crates/oracles/{conservation,idempotence,transport}/`
- Fixtures: under each TS package: `fixtures/*.json`; mirror minimal fixtures in Rust tests.

## PR Body — required
Every PR must use the repo’s PR template and include: Summary, Evidence (artifact checklist), Determinism & Seeds, Tests & CI, Implementation Notes, Hurdles/Follow‑ups.

## Early‑stop guardrails
Do **NOT** stop after infra‑only tweaks. Stop **only** when:
1) All T3 artifacts exist and are stable across two runs.
2) TS & Rust tests pass; parity for all three oracles is **true**.
3) PR is opened with a completed PR body (template sections present).
