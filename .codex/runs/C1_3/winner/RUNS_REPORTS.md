# Parallel run aggregation
_Winner branch: main — 2025-09-13T01:11:50Z_

---

## Run A — PR #42 (6a7233a)
_C1 pass-3: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Minimal host exposes only `POST /plan` and `POST /apply` with canonical error handling【F:packages/host-lite/src/server.ts†L96-L116】【F:packages/host-lite/tests/host-lite.test.ts†L63-L77】
- EG-2: Responses and journals are byte-identical on repeats and proofs gate on `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L12-L48】
- EG-3: State is ephemeral; per-world cache capped at 32 entries (LRU) across worlds【F:packages/host-lite/src/server.ts†L9-L36】【F:packages/host-lite/tests/host-lite.test.ts†L87-L99】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L132】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Added raw handler to expose 400 errors without opening sockets.
- Multi-world cache test proves per-world LRU bound.
- Export added for tests but remains within package boundary.
- Node `http` keeps runtime dependencies minimal.
- Canonicalization centralized via `tf-lang-l0` utilities.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 3

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
- [x] Do not edit `.codex/tasks/**` — confirmed
- [x] No new runtime deps — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No `as any`; ESM imports include `.js`; no per-call locks; no cross-test bleed — code/test link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply`; outputs deterministic — test link: packages/host-lite/tests/host-lite.test.ts

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
# Observation Log — C1 — Run 3

- Strategy chosen: Tightened host-lite with raw handler for 400s and multi-world LRU checks.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json; CHANGES.md; COMPLIANCE.md; OBS_LOG.md; REPORT.md
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: ensured tests avoid sockets; added export to test raw parsing.
- Notes: proof hashing skipped when DEV_PROOFS!=1; cache capped at 32 entries/world.
```

### CHANGES.md
```md
# C1 — Changes (Run 3)

## Summary
Refined `host-lite` to enforce canonical error handling and deterministic responses. Added raw request parsing with 400/404 coverage, multi-world LRU bounds, and packaging exports for clarity.

## Why
- Meets END_GOAL by keeping host minimal while ensuring idempotent, bounded `/plan` and `/apply` with canonical bytes.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts` now checks 400/404 models, multi-world cache bounds, and byte-level determinism.
- Updated: none
- Determinism/parity: `pnpm test` repeats are stable and avoid sockets/files.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
```

---

## Run B — PR #43 (cbcc798)
_C1 pass-3: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Minimal host exposes only `/plan` and `/apply` via Node HTTP【F:packages/host-lite/src/server.ts†L74-L83】
- EG-2: Canonical, idempotent responses with bounded per-world cache【F:packages/host-lite/src/server.ts†L20-L71】【F:packages/host-lite/tests/host-lite.test.ts†L13-L44】【F:packages/host-lite/tests/host-lite.test.ts†L81-L99】
- EG-3: Proofs gated by `DEV_PROOFS` with no cost when off【F:packages/host-lite/src/server.ts†L49-L53】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】
- EG-4: Error model returns canonical 404/400 bodies【F:packages/host-lite/src/server.ts†L85-L110】【F:packages/host-lite/tests/host-lite.test.ts†L59-L76】【F:packages/host-lite/tests/host-lite.test.ts†L100-L113】
- EG-5: State stays in-memory and resets on new host creation【F:packages/host-lite/tests/host-lite.test.ts†L47-L56】

## Blockers honored
- B-1: ✅ Deterministic in-memory host with LRU cache cap 32【F:packages/host-lite/src/server.ts†L10-L37】【F:packages/host-lite/tests/host-lite.test.ts†L81-L99】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` gated; zero overhead when disabled【F:packages/host-lite/src/server.ts†L49-L53】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】

## Lessons / tradeoffs (≤5 bullets)
- Node HTTP only; no new runtime deps.
- Cache cap 32 balances determinism and memory; multi-world test proves bound.
- Parsing moved to handler to surface 400s without sockets.
- Boundary scan limited to package to avoid repo-wide false positives.
- Canonicalization centralized in single exec path.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 3

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: packages/host-lite/src/server.ts
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports include `.js` — code link: packages/host-lite/tests/host-lite.test.ts
- [x] Tests run in parallel without cross-test state bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Outputs deterministic via canonical bytes — code/test link: packages/host-lite/src/server.ts
- [x] Host uses in-memory state only — code link: packages/host-lite/src/server.ts
- [x] Endpoints limited to `/plan` and `/apply` — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No new runtime dependencies — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net writes) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No per-call locks; no cross-test global state bleed — code/test link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply`; outputs deterministic — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS
- [x] Do not edit `.codex/tasks/**` — n/a
- [x] No new runtime deps; Fastify removed — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No `as any`; ESM imports keep `.js` — code link: packages/host-lite/tests/host-lite.test.ts
- [x] Only `/plan` and `/apply`; deterministic outputs — test link: packages/host-lite/tests/host-lite.test.ts

## Acceptance (oracle)
- [x] Enable/disable behavior (both runtimes)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (e.g., ESM)
- [x] Code quality (naming, no unnecessary clones/copies)
- [x] 404/400 canonical errors — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Multi-world cache bound proof — test link: packages/host-lite/tests/host-lite.test.ts

## Evidence
- Code: packages/host-lite/src/server.ts; packages/host-lite/package.json
- Tests: packages/host-lite/tests/host-lite.test.ts
- CI runs: pnpm test
- Bench (off-mode, if applicable): n/a
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 3

- Strategy chosen: Hardened host-lite error paths and cache proofs while maintaining zero-dep runtime.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json
- Determinism stress (runs × passes): 3×; stable outputs.
- Near-misses vs blockers: boundary scan kept local to host-lite to avoid false positives.
- Notes: proofs hashed only when DEV_PROOFS=1; per-world cache capped at 32.
```

### CHANGES.md
```md
# C1 — Changes (Run 3)

## Summary
Refined `host-lite` to harden error handling and determinism. Added explicit malformed JSON 400s, method gating, and multi-world LRU proofs while keeping proofs gated.

## Why
- Advances END_GOAL by ensuring canonical idempotent `/plan` and `/apply` responses with bounded per-world cache and proof toggling.

## Tests
- Added: malformed JSON 400, method 404, multi-world cache bounds.
- Updated: boundary scan for package imports.
- Determinism/parity: repeated `pnpm test` runs stable; no sockets/files/network.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
```

---

## Run C — PR #44 (048ecf9)
_C1 pass-3: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Minimal host exposes only `/plan` and `/apply` via Node HTTP【F:packages/host-lite/src/server.ts†L96-L104】
- EG-2: Idempotent, canonical responses with bounded cache【F:packages/host-lite/src/server.ts†L12-L66】【F:packages/host-lite/tests/host-lite.test.ts†L12-L25】【F:packages/host-lite/tests/host-lite.test.ts†L76-L90】
- EG-3: Journal entries canonical with proofs gated by `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L27-L46】
- EG-4: State is in-memory and resets on new host creation【F:packages/host-lite/tests/host-lite.test.ts†L48-L56】
- EG-5: Error paths return canonical bodies: 404 for unknown routes, 400 for bad JSON【F:packages/host-lite/src/server.ts†L96-L104】【F:packages/host-lite/src/server.ts†L112-L125】【F:packages/host-lite/tests/host-lite.test.ts†L60-L74】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L91】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Node HTTP keeps runtime deps slim (only `tf-lang-l0`).
- LRU cache (32 entries/world) prevents growth across multiple worlds.
- Optional body argument allowed hermetic 400 tests without sockets.
- Package export clarifies boundary; no deep relative imports.
- Canonicalization centralized through `tf-lang-l0` helpers.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 3

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
- [x] No edits under `.codex/tasks/**` — implicit (none touched)
- [x] No new runtime deps — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No `as any`; ESM imports include `.js` — code link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply` with deterministic outputs — test link: packages/host-lite/tests/host-lite.test.ts

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
# Observation Log — C1 — Run 3

- Strategy chosen: Tightened host-lite surface with centralized JSON canonicalization and explicit error paths.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json
- Determinism stress (runs × passes): 3×; stable outputs.
- Near-misses vs blockers: ensuring hermetic 400 test without sockets required optional body in handler.
- Notes: per-world cache cap retained at 32; proofs hashed only when `DEV_PROOFS=1`.
```

### CHANGES.md
```md
# C1 — Changes (Run 3)

## Summary
Hardened `host-lite` with canonical error bodies (400 for malformed JSON, 404 otherwise), multi-world LRU cache bounds, and gated proofs with zero overhead when disabled. Package now exports `src/server.ts` directly for clarity.

## Why
- Ensures idempotent, deterministic `/plan` and `/apply` while bounding per-world cache and keeping responses canonical.

## Tests
- Added: extended `packages/host-lite/tests/host-lite.test.ts` for 400/404, multi-world cache caps, packaging and boundary scans.
- Updated: none
- Determinism/parity: repeated runs via `pnpm test` are stable and socket-free.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
```

---

## Run D — PR #45 (0f1cb92)
_C1 pass-3: host-lite refinement_

### REPORT.md
```md
# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Host packaged only in `packages/host-lite` with `/plan` and `/apply` routes【F:packages/host-lite/src/server.ts†L96-L101】【F:packages/host-lite/package.json†L2-L9】
- EG-2: Canonical deterministic responses via L0 helpers【F:packages/host-lite/src/server.ts†L45-L66】【F:packages/host-lite/tests/host-lite.test.ts†L12-L24】
- EG-3: Journal proofs gated behind `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】
- EG-4: Per-world LRU cache (cap 32) preserves idempotency without growth【F:packages/host-lite/src/server.ts†L9-L36】【F:packages/host-lite/tests/host-lite.test.ts†L75-L97】
- EG-5: HTTP parser yields canonical 400/404 errors【F:packages/host-lite/src/server.ts†L105-L118】【F:packages/host-lite/tests/host-lite.test.ts†L59-L73】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L139】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Default cache cap 32 balances replay speed with bounded memory; tested across multiple worlds.
- Centralized `handleHttp` avoids framework deps and ensures uniform error bodies.
- Package exports point to `dist/` to stay aligned with `tf-lang-l0` packaging.
- Tests stay hermetic by invoking handlers directly—no sockets or FS writes.
- Only runtime dep remains `tf-lang-l0`; Node `http` covers transport.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 3

# Blockers (must all be ✅)
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
- [x] Do not edit `.codex/tasks/**` — none touched
- [x] No new runtime deps; only `tf-lang-l0` — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No `as any` casts; ESM imports keep `.js`; no per-call locks — code link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply` endpoints; outputs deterministic — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Multi-world cache cap enforced — test link: packages/host-lite/tests/host-lite.test.ts

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
# Observation Log — C1 — Run 3

- Strategy chosen: Harden host-lite with explicit build outputs, HTTP parsing helper, and expanded tests for error paths and cache bounds.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json; packages/host-lite/tsconfig.json
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: `vitest` missing after rename; fixed via install.
- Notes: proof hashing skipped when DEV_PROOFS!=1; cache capped at 32 entries per world with per-world LRU.
```

### CHANGES.md
```md
# C1 — Changes (Run 3)

## Summary
Refined `packages/host-lite` as the sole host package with explicit build outputs and centralized HTTP parsing. Added canonical 400/404 errors and expanded LRU tests to cover multi‑world caps.

## Why
- Satisfies END_GOAL: minimal in-memory host with deterministic `/plan` and `/apply` routes and ephemeral state.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts` now covers 400/404 errors, multi-world LRU bounds, packaging, and boundary scan.
- Updated: host-lite package build configuration.
- Determinism/parity: repeated runs via `pnpm test` are stable and socket-free.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
```
