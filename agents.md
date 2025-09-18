## Agents — T3 Oracles Epic (Conservation • Idempotence • Transport)

**Mission:** Implement the next three cross-runtime oracles and wire them into CI with deterministic, canonical artifacts:

* **T3\_1 — Conservation** (TS + Rust)
* **T3\_2 — Idempotence** (TS + Rust)
* **T3\_3 — Transport** (serialize/round-trip) (TS + Rust)
* **T3\_4 — Parity & Contract Tests** (TS↔Rust parity for each oracle)
* **T3\_5 — CI & Docs** (jobs, artifacts, PR reporting)

### Rails (must NOT violate)

* **Deterministic:** stable key order; canonical JSON; fixed `now` in tests; repeat determinism **2×**.
* **No runtime deps** (devDeps OK for build/test).
* **TS:** ESM with internal imports ending in **`.js`**; no deep cross-package imports; no `as any`.
* **Rust:** no `static mut`; no panicking `unwrap/expect` in libraries; prefer `Result`; use `BTree*` for ordering.
* Reuse shared helpers from **`@tf-lang/utils`** and **oracles core**; **do not** duplicate utilities.
* Tests are offline/reproducible; seeds checked in.

### ABI (stable from T1 core)

* **TS:** `Oracle<I,O>(input, ctx) -> Promise<OracleResult>` from `@tf-lang/oracles-core-ts`.
* **Rust:** analogous traits/types from `tf-oracles-core`.
* **Do not change** the public ABI of the core; implement new oracles as add-on packages/crates.

### Artifacts (required for CI green)

* `out/t3/conservation/report.json`
* `out/t3/idempotence/report.json`
* `out/t3/transport/report.json`
* `out/t3/parity/{conservation,idempotence,transport}.json` with `{ "equal": true, ... }`

All artifacts must be canonical JSON with a trailing newline.

### Folder targets

* **TS:** `packages/oracles/{conservation,idempotence,transport}/`
* **Rust:** `crates/oracles/{conservation,idempotence,transport}/`
* **Fixtures:** TS `fixtures/*.json`; mirror minimal fixtures in Rust tests.

### PR body — required

Use the repo PR template with: **Summary**, **Evidence** (artifact checklist), **Determinism & Seeds**, **Tests & CI**, **Implementation Notes**, **Hurdles/Follow-ups**.