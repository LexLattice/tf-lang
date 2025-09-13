# Parallel run aggregation
_Winner branch: main — 2025-09-12T23:18:18Z_

---

## Run A — PR #38 (1764f93)
_C1 pass-2: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 2

## End Goal fulfillment
- EG-1: Minimal host exposes only `/plan` and `/apply` via Node HTTP【F:packages/host-lite/src/server.ts†L96-L101】
- EG-2: Idempotent, canonical responses with bounded cache【F:packages/host-lite/src/server.ts†L12-L66】【F:packages/host-lite/tests/host-lite.test.ts†L12-L25】【F:packages/host-lite/tests/host-lite.test.ts†L67-L74】
- EG-3: Journal entries canonical with proofs gated by `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】
- EG-4: State is in-memory and resets on new host creation【F:packages/host-lite/tests/host-lite.test.ts†L47-L56】
- EG-5: Non-endpoints return explicit 404 with canonical body【F:packages/host-lite/src/server.ts†L98-L101】【F:packages/host-lite/tests/host-lite.test.ts†L59-L65】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L92】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Node HTTP removed third-party runtime dependencies.
- LRU cache (32 entries/world) enforces idempotency without memory growth.
- Public export of `DummyHost` avoids deep relative imports.
- Direct handler testing keeps suite hermetic and parallel-safe.
- Canonicalization centralized through `tf-lang-l0` helpers.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 2

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: packages/host-lite/src/server.ts
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports must include `.js` — code link: packages/host-lite/src/server.ts
- [x] Tests run in parallel without cross-test state bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — code/test link: packages/host-lite/src/server.ts
- [x] Host must not use files or external DBs; in-memory only — code link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply` endpoints are allowed — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` must be idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS
- [x] No new runtime deps; Fastify removed — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No `as any` casts; ESM imports keep `.js` — code link: packages/host-lite/src/server.ts
- [x] Endpoint list fixed and outputs deterministic — test link: packages/host-lite/tests/host-lite.test.ts

## Acceptance (oracle)
- [x] Enable/disable behavior (both runtimes)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (e.g., ESM)
- [x] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: packages/host-lite/src/server.ts
- Tests: packages/host-lite/tests/host-lite.test.ts
- CI runs: pnpm test
- Bench (off-mode, if applicable): n/a
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 2

- Strategy chosen: Migrated host to package with Node HTTP server and LRU cache.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/tf-lang-l0-ts/src/index.ts; pnpm-lock.yaml
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: needed package export to avoid deep imports.
- Notes: proof hashing skipped when DEV_PROOFS!=1; cache capped at 32 entries per world.
```

### CHANGES.md
```md
# C1 — Changes (Run 2)

## Summary
Replaced Fastify host with a bare Node HTTP server packaged under `packages/host-lite`. Added bounded LRU caching and 404 handling to keep responses canonical and idempotent without unbounded growth.

## Why
- Satisfies END_GOAL: minimal in-memory host with deterministic `/plan` and `/apply` routes and ephemeral state.

## Tests
- Added: extended `packages/host-lite/tests/host-lite.test.ts` for idempotency, proof gating, 404s, cache bounds, boundary scan.
- Updated: none
- Determinism/parity: repeated runs via `pnpm test` are stable and socket-free.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
```

---

## Run B — PR #39 (ef595bf)
_C1 pass-2: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 2

## Targeted Goals
- Packaging clarity: host exists as a leaf package exposing only `POST /plan` and `POST /apply`; other paths return 404【F:packages/host-lite/src/index.ts†L15-L22】【F:packages/host-lite/src/index.ts†L76-L78】
- Canonical determinism: responses and proofs derive from `canonicalJsonBytes`, ensuring byte-stable output【F:packages/host-lite/src/index.ts†L24-L41】【F:packages/host-lite/src/index.ts†L44-L67】
- Idempotency without growth: `apply` caches only the last request per world, preventing cache expansion【F:packages/host-lite/src/index.ts†L44-L67】【F:packages/host-lite/tests/host-lite.test.ts†L75-L82】
- Proof gating: proof hashes computed only when `DEV_PROOFS=1`【F:packages/host-lite/src/index.ts†L35-L38】【F:packages/host-lite/src/index.ts†L60-L63】
- Test hardening: explicit 404 handling and hermetic tests using in-memory `Request` objects【F:packages/host-lite/src/index.ts†L76-L78】【F:packages/host-lite/tests/host-lite.test.ts†L67-L73】
- Dependency slim: runtime uses only Node built-ins; Fastify removed.
- Public boundaries only: host consumes `DummyHost` via new public export【F:packages/tf-lang-l0-ts/src/index.ts†L6-L9】

## Memory approach
Caching retains only the most recent `apply` result per world, replacing prior entries so a sequence of distinct requests leaves cache size constant【F:packages/host-lite/src/index.ts†L44-L67】【F:packages/host-lite/tests/host-lite.test.ts†L75-L82】

## Tests
- `pnpm build`
- `pnpm test`
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 2

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas — code: `packages/host-lite/src/index.ts`
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code: `packages/host-lite/src/index.ts`
- [x] ESM internal imports include `.js` — code: `packages/host-lite/tests/host-lite.test.ts`
- [x] Tests run in parallel without cross-test state bleed — test: `packages/host-lite/tests/host-lite.test.ts`
- [x] Outputs deterministic (canonical JSON & hashes) — code/test: `packages/host-lite/src/index.ts`, `packages/host-lite/tests/host-lite.test.ts`
- [x] Host uses in-memory state only; no external persistence — code: `packages/host-lite/src/index.ts`
- [x] Only `/plan` and `/apply` endpoints exposed — code: `packages/host-lite/src/index.ts`
- [x] `/plan` and `/apply` are idempotent — test: `packages/host-lite/tests/host-lite.test.ts`
- [x] Proof artifacts gated behind `DEV_PROOFS=1` — test: `packages/host-lite/tests/host-lite.test.ts`

## EXTRA BLOCKERS
- [x] No new runtime dependencies; removed Fastify.
- [x] Tests hermetic (no sockets/files/network) — test: `packages/host-lite/tests/host-lite.test.ts`
- [x] No `as any` casts; ESM imports keep `.js` — code/test links above.
- [x] Endpoint surface fixed; outputs deterministic — code: `packages/host-lite/src/index.ts`
- [x] No deep cross-package imports; only public exports — code: `packages/host-lite/src/index.ts`

## Acceptance (oracle)
- [x] Idempotent plan/apply responses — `packages/host-lite/tests/host-lite.test.ts`
- [x] Canonical journals and proof gating — `packages/host-lite/tests/host-lite.test.ts`
- [x] Isolation: host is in-memory and ephemeral — `packages/host-lite/tests/host-lite.test.ts`
- [x] 404 for non-endpoints — `packages/host-lite/tests/host-lite.test.ts`

## Evidence
- Code: `packages/host-lite/src/index.ts`; `packages/tf-lang-l0-ts/src/index.ts`
- Tests: `packages/host-lite/tests/host-lite.test.ts`
- CI runs: `pnpm build`, `pnpm test`
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 2

- Strategy: replace Fastify service with native HTTP handler in a leaf package.
- Key changes: `packages/host-lite/**`, `packages/tf-lang-l0-ts/src/index.ts`, `packages/tf-lang-l0-ts/package.json`, `pnpm-lock.yaml`.
- Determinism stress: repeated plan/apply and 404 routes; cache remained constant.
- Near-misses: build initially emitted tests and missing package entry; fixed tsconfig and package.json.
- Notes: cache stores only last apply per world; no third-party HTTP runtime deps.
```

### CHANGES.md
```md
# C1 — Changes (Run 2)

## Summary
Refactored the Fastify host service into a leaf package (`packages/host-lite`) using
native HTTP primitives. The package exposes only `POST /plan` and `POST /apply`,
centralizes canonical JSON and proof hashing, bounds idempotent caching, and
returns 404 for any other path.

## Why
- Aligns with Pass‑2 goals: single host package, deterministic canonicalization,
idempotency without unbounded growth, and optional proofs.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts`
- Updated: `packages/tf-lang-l0-ts/src/index.ts`
- Determinism/parity: repeated runs yield byte‑identical responses and constant cache size.

## Notes
- Removed Fastify; no third‑party runtime HTTP dependencies.
```

---

## Run C — PR #40 (42da406)
_C1 pass-2: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 2

## Targeted Goals
- TG-1: Host lives only in `packages/host-lite` and serves just `/plan` and `/apply`【F:packages/host-lite/src/server.ts†L11-L55】
- TG-2: Canonical JSON and hashing delegated to `tf-lang-l0`; repeat calls are byte-identical【F:packages/host-lite/src/server.ts†L39-L46】【F:packages/host-lite/tests/host-lite.test.ts†L11-L20】
- TG-3: Idempotent cache bounded to 16 entries preventing unbounded growth【F:packages/host-lite/src/server.ts†L46-L49】【F:packages/host-lite/tests/host-lite.test.ts†L63-L68】
- TG-4: Proofs emitted only when `DEV_PROOFS=1`; otherwise no hashing cost【F:packages/host-lite/src/server.ts†L41-L43】【F:packages/host-lite/tests/host-lite.test.ts†L22-L41】
- TG-5: Explicit 404 for non-endpoints with canonical body【F:packages/host-lite/src/server.ts†L15-L18】【F:packages/host-lite/tests/host-lite.test.ts†L56-L60】
- TG-6: Runtime uses no third-party HTTP framework; built on `node:http`【F:packages/host-lite/src/server.ts†L1】
- TG-7: No deep cross-package imports; `DummyHost` exported publicly【F:packages/tf-lang-l0-ts/src/index.ts†L2-L9】【F:packages/host-lite/tests/host-lite.test.ts†L71-L74】

## Blockers honored
- B-1: ✅ Only `/plan` and `/apply` endpoints, in-memory state, deterministic output【F:packages/host-lite/src/server.ts†L11-L55】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with canonical serialization【F:packages/host-lite/tests/host-lite.test.ts†L22-L41】

## Lessons / tradeoffs (≤5 bullets)
- Dropping Fastify slimmed dependencies but required custom request handling.
- Exporting `DummyHost` opened minimal public surface for host integration.
- Bounded maps avoid memory growth at the cost of occasional cache eviction.
- Direct handler tests keep suite hermetic without network sockets.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 2

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: packages/host-lite/src/server.ts
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports must include `.js` — code link: packages/host-lite/src/server.ts
- [x] Tests run in parallel without cross-test state bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — code/test link: packages/host-lite/src/server.ts
- [x] Host must not use files or external DBs; in-memory only — code link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply` endpoints are allowed — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` must be idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts

## Extra Blockers
- [x] No new runtime deps; Fastify removed — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/network/FS writes) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Endpoint list fixed and deterministic outputs — code link: packages/host-lite/src/server.ts

## Acceptance (oracle)
- [x] Enable/disable behavior (both runtimes)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (e.g., ESM)
- [x] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: packages/host-lite/src/server.ts
- Tests: packages/host-lite/tests/host-lite.test.ts
- CI runs: pnpm --filter tf-lang-l0 test && pnpm --filter host-lite test
- Bench (off-mode, if applicable): n/a
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 2

- Strategy chosen: remove Fastify; custom `node:http` host with bounded cache and public L0 exports.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/tf-lang-l0-ts/src/index.ts; pnpm-lock.yaml
- Determinism stress (runs × passes): 2×; stable outputs and 404 coverage.
- Near-misses vs blockers: package import failed until `tf-lang-l0` exported `DummyHost`.
- Notes: cache capped at 16 entries to avoid growth; DEV_PROOFS toggled in tests.
```

### CHANGES.md
```md
# C1 — Changes (Run 2)

## Summary
Moved the host to a single `packages/host-lite` leaf package and replaced Fastify with a
minimal `node:http` implementation exposing only `POST /plan` and `POST /apply`. Responses
are canonically serialized, proof emission is gated by `DEV_PROOFS`, and caches are bounded
to avoid memory growth.

## Why
- Aligns with END_GOAL and pass‑2 targets: centralized canonicalization, bounded idempotent
behaviour, and dependency‑slim runtime.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts`
- Updated: `packages/tf-lang-l0-ts/src/index.ts`
- Determinism/parity: repeated calls yield byte‑identical outputs; 404 paths handled.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
```

---

## Run D — PR #41 (937bb4e)
_C1 pass-2: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 2

## End Goal fulfillment
- EG-1: Leaf package `host-lite` exposes only `POST /plan` and `POST /apply` via built-in HTTP handler【F:packages/host-lite/src/index.ts†L27-L64】
- EG-2: Repeated calls are idempotent and canonical; state resets on new host【F:packages/host-lite/tests/host-lite.test.ts†L11-L20】【F:packages/host-lite/tests/host-lite.test.ts†L45-L55】
- EG-3: Journal entries are canonical with proofs gated behind `DEV_PROOFS`【F:packages/host-lite/src/index.ts†L52-L57】【F:packages/host-lite/tests/host-lite.test.ts†L22-L43】

## Targeted goals
- TG-1 Packaging clarity: single leaf package with two routes【F:packages/host-lite/src/index.ts†L27-L64】
- TG-2 Canonical determinism centralized via L0 helpers【F:packages/host-lite/src/index.ts†L33-L59】
- TG-3 Idempotency without growth: bounded cache limits worlds and entries【F:packages/host-lite/src/index.ts†L12-L21】【F:packages/host-lite/tests/host-lite.test.ts†L65-L72】
- TG-4 Proof gating intact: proofs emitted only when `DEV_PROOFS=1`【F:packages/host-lite/src/index.ts†L55-L57】【F:packages/host-lite/tests/host-lite.test.ts†L22-L43】
- TG-5 Test hardening: 404 for non-endpoints and hermetic tests【F:packages/host-lite/src/index.ts†L27-L31】【F:packages/host-lite/tests/host-lite.test.ts†L57-L63】
- TG-6 Dependency slim: no third-party HTTP framework, only built-ins【F:packages/host-lite/package.json†L1-L18】
- TG-7 Public boundaries only: host imports through `tf-lang-l0` export surface【F:packages/host-lite/src/index.ts†L1】【F:packages/tf-lang-l0-ts/src/index.ts†L2-L9】【F:packages/tf-lang-l0-ts/package.json†L1-L8】

## Blockers honored
- B-1: ✅ Only `/plan` and `/apply`, in-memory state, deterministic outputs【F:packages/host-lite/src/index.ts†L27-L64】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS`, no per-call locks or `as any`【F:packages/host-lite/src/index.ts†L55-L57】

## Lessons / tradeoffs (≤5 bullets)
- Bounded caches prevent unbounded memory growth while preserving idempotency.
- Removing Fastify reduced dependency surface but required custom routing logic.
- Exporting `DummyHost` enabled public boundary adherence.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 2

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: packages/host-lite/src/index.ts
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — code link: packages/host-lite/src/index.ts
- [x] ESM internal imports must include `.js` — code/test link: packages/host-lite/src/index.ts; packages/host-lite/tests/host-lite.test.ts
- [x] Tests run in parallel without cross-test state bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — code/test link: packages/host-lite/src/index.ts; packages/host-lite/tests/host-lite.test.ts
- [x] Host must not use files or external DBs; in-memory only — code link: packages/host-lite/src/index.ts
- [x] Only `/plan` and `/apply` endpoints are allowed — code link: packages/host-lite/src/index.ts
- [x] `/plan` and `/apply` must be idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS
- [x] No new runtime deps unless necessary — `packages/host-lite/package.json`
- [x] Tests are hermetic: no open sockets or network calls — `packages/host-lite/tests/host-lite.test.ts`
- [x] Explicit 404 for non-endpoints — `packages/host-lite/src/index.ts`
- [x] No deep relative imports across packages — `packages/host-lite/tests/host-lite.test.ts`

## Acceptance (oracle)
- [x] Enable/disable behavior (proof gating)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (ESM, public exports)
- [x] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: packages/host-lite/src/index.ts; packages/tf-lang-l0-ts/src/index.ts
- Tests: packages/host-lite/tests/host-lite.test.ts
- CI runs: `pnpm -F tf-lang-l0 test`, `pnpm -F host-lite test`
- Bench (off-mode, if applicable): n/a
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 2

- Strategy chosen: replaced Fastify with native `node:http`; wrapped logic in leaf package with bounded caches.
- Key changes (files): packages/host-lite/src/index.ts; packages/host-lite/tests/host-lite.test.ts; packages/tf-lang-l0-ts/src/index.ts
- Determinism stress (runs × passes): tests repeated 2×; outputs stable.
- Near-misses vs blockers: had to add `exports` field to `tf-lang-l0` to avoid deep imports.
- Notes: cache limit keeps memory bounded; dependency surface minimized.
```

### CHANGES.md
```md
# C1 — Changes (Run 2)

## Summary
Replaced the Fastify service with a leaf package `packages/host-lite` using only built-in `node:http`. The host now exposes just `POST /plan` and `POST /apply`, serves canonical responses, and bounds in-memory caches.

## Why
Delivers pass-2 goals: clarified packaging, centralized canonicalization, bounded idempotent caching, explicit 404 handling, and removal of third-party HTTP frameworks.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts`
- Updated: export surface in `packages/tf-lang-l0-ts/src/index.ts`
- Determinism/parity: repeated tests confirm byte-identical outputs and proof gating.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
```
