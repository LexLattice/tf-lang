# Parallel run aggregation
_Winner branch: main — 2025-09-13T04:11:57Z_

---

## Run A — PR #54 (a930722)
_D1 pass-2: SQLite adapter hardening (param queries, SQL paging, types)_

### REPORT.md
```md
# REPORT — C1 — Run 4

## Goal → Evidence map
- G1 Raw path unified; `createServer` delegates to `makeRawHandler`【F:packages/host-lite/src/server.ts:93】【F:packages/host-lite/src/server.ts:106】
- G2 Endpoints only POST `/plan` and `/apply`; otherwise 404【F:packages/host-lite/src/server.ts:84】【F:packages/host-lite/test/c1.http-400-404.test.ts:6】
- G3 Determinism: `/plan` and `/apply` produce byte-identical responses【F:packages/host-lite/test/c1.byte-determinism.test.ts:7】
- G4 Proof gating: DEV_PROOFS toggles tags; count check【F:packages/host-lite/src/server.ts:58】【F:packages/host-lite/test/c1.proofs-gating-count.test.ts:6】
- G5 LRU bounds: per-world cap 32; map size equals worlds touched【F:packages/host-lite/src/server.ts:9】【F:packages/host-lite/test/c1.lru-multiworld.test.ts:4】
- G6 Hygiene: ESM internal `.js`; public exports only; no deep imports【F:packages/host-lite/test/c1.import-hygiene.test.ts:1】
- G7 Packaging: `main` and `exports` both `src/server.ts`【F:packages/host-lite/package.json:7】

## Notes & tradeoffs
- Centralized parsing simplifies server wiring and ensures canonical error bodies.
- Shared `exec` path guarantees identical planning/apply response shapes and bytes.
- LRU scoped per world prevents cross-world interference and growth.

## Determinism runs
- Repeated `pnpm -F host-lite-ts test` stable across 5 runs (documented in OBS_LOG.md).

# REPORT — D1 — Run 1

## End Goal fulfillment
- EG-1: SQLite adapter serves counts and clauses via CLI-backed queries【F:services/claims-api-ts/src/db.ts†L10-L42】
- EG-2: Responses expose `dataset_version` and BLAKE3 `query_hash` with ≥10 evidence samples【F:services/claims-api-ts/src/db.ts†L37-L41】【F:services/claims-api-ts/src/util.ts†L2-L7】【F:services/claims-api-ts/test/sqlite.test.ts†L34-L45】

## Blockers honored
- B-1: ✅ Storage uses SQLite only (no JSON queries)【F:services/claims-api-ts/src/db.ts†L28-L30】
- B-2: ✅ Identical queries return stable results【F:services/claims-api-ts/test/sqlite.test.ts†L34-L55】

## Lessons / tradeoffs (≤5 bullets)
- Switched from JS libraries to `sqlite3` CLI for deterministic, zero-dep storage.
- Evidence sampling fixed at first 10 ordered rows for stability.
- Canonical JSON hashing guarantees query-key determinism.

## Bench notes (optional, off-mode)
- n/a

# REPORT — D1 — Run 2

## End Goal fulfillment
- EG-1: In-memory sql.js database built from schema/seed fixtures; queries are ordered for determinism【F:packages/d1-sqlite/src/db.js†L1-L15】【F:services/claims-api-ts/src/db.ts†L23-L47】
- EG-2: Responses expose dataset version and BLAKE3 `query_hash` with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L32-L47】【F:services/claims-api-ts/test/sqlite.test.ts†L18-L30】

## Blockers honored
- B-1: ✅ No SQLite binaries tracked; ignore rules added【F:.gitignore†L62-L65】【F:services/claims-api-ts/test/sqlite.test.ts†L6-L10】
- B-2: ✅ Only `sql.js` imported; repeated queries byte-identical【F:services/claims-api-ts/src/server.ts†L1-L43】【F:services/claims-api-ts/test/sqlite.test.ts†L12-L24】

## Lessons / tradeoffs
- Replaced native CLI with WASM `sql.js` for portability.
- Fixture-driven dataset keeps tests hermetic and deterministic.
- Memoized in-memory DB avoids filesystem I/O.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.

# REPORT — D1 — Run pass-2

## End Goal fulfillment
- EG-1: SQLite adapter uses parameterized queries with SQL paging and ORDER BY for determinism【F:services/claims-api-ts/src/db.ts†L27-L98】
- EG-2: Responses include dataset version and BLAKE3 query hashes with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L47-L72】【F:services/claims-api-ts/test/sqlite.test.ts†L51-L60】

## Blockers honored
- B-1: ✅ Storage uses in-memory SQLite only【F:services/claims-api-ts/src/db.ts†L1-L98】
- B-2: ✅ Identical queries return stable results with ≥10 evidence samples【F:services/claims-api-ts/test/sqlite.test.ts†L51-L68】

## Lessons / tradeoffs (≤5 bullets)
- Parameterized statements add verbosity but ensure injection safety.
- SQL-side LIMIT/OFFSET avoids JS paging and preserves determinism.
- Exported Fastify instance enables hermetic HTTP validation.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 4

## Blockers (must all be ✅)
- [x] No kernel/schema changes — code link: packages/host-lite/src/server.ts
- [x] No per-call locks or `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports include `.js` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Tests parallel-safe, no global bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Deterministic canonical outputs — code/test link: packages/host-lite/src/server.ts
- [x] In-memory host only `/plan` & `/apply` — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proofs gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Per-world LRU cache cap 32 — code/test link: packages/host-lite/src/server.ts
- [x] No new runtime dependencies — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/network) — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No new runtime deps — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/fs/network side-effects) — test link: packages/host-lite/test/c1.http-400-404.test.ts
- [x] Public-exports only (no deep relative imports) — test link: packages/host-lite/test/c1.import-hygiene.test.ts
- [x] Do not edit `.codex/tasks/**` — n/a
- [x] Package exports remain `src/server.ts` — code link: packages/host-lite/package.json

## Acceptance (oracle)
- [x] Enable/disable behavior
- [x] Cache cold→warm; reset forces re-read
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (ESM)
- [x] Code quality (minimal diff)
- [x] 404/400 canonical errors — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Multi-world cache bound proof — test link: packages/host-lite/tests/host-lite.test.ts

## Evidence
- Code: packages/host-lite/src/server.ts; packages/host-lite/package.json
- Tests: packages/host-lite/test/c1.byte-determinism.test.ts; packages/host-lite/test/c1.proofs-gating-count.test.ts; packages/host-lite/test/c1.http-400-404.test.ts; packages/host-lite/test/c1.lru-multiworld.test.ts; packages/host-lite/test/c1.import-hygiene.test.ts
- Runs: `pnpm -F host-lite-ts test`
- Bench (off-mode, if applicable): n/a

# COMPLIANCE — D1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks or `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js` — code link: services/claims-api-ts/src/server.ts
- [x] Tests parallel-safe, deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage strictly SQLite — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Identical queries stable; ≥10 evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Storage via SQLite only
- [x] Hashes/versions match expected
- [x] Stability across identical queries
- [x] ≥10 evidence samples per response
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts
- Tests: services/claims-api-ts/test/sqlite.test.ts
- CI runs: `pnpm --filter claims-api-ts test`
- Bench: n/a

# COMPLIANCE — D1 — Run 2

## Blockers (must all be ✅)
- [x] Remove repo-tracked DB; ignore SQLite artifacts — code link: .gitignore
- [x] Storage via in-memory sql.js builder with fixtures — code link: packages/d1-sqlite/src/db.js
- [x] All queries ORDER BY; no `as any`; ≥10 evidence — code link: services/claims-api-ts/src/db.ts
- [x] Responses expose dataset version and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Tests hermetic; no binaries tracked — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] `git ls-files` returns no `.db` or `.sqlite` files
- [x] Stability across identical queries
- [x] ≥10 evidence samples per count response
- [x] Storage proof: only `sql.js` imported
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run pass-2

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks or `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js` — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests parallel-safe, deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage strictly SQLite — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Identical queries stable; ≥10 evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-2)
- [x] Parameterized SQL queries only — code link: services/claims-api-ts/src/db.ts
- [x] No JS paging; SQL `LIMIT/OFFSET` — code/test link: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] Input validation; 400 for invalid shapes — code/test link: services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] Injection-shaped value safe — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] No committed DB binaries — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ESM hygiene scan — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Storage via SQLite only
- [x] Hashes/versions match expected
- [x] Stability across identical queries
- [x] ≥10 evidence samples per response
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/src/types.ts
- Tests: services/claims-api-ts/test/sqlite.test.ts
- CI runs: `pnpm --filter claims-api-ts test`; `pnpm test`
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run pass-2

- Strategy: parameterize SQL queries and move paging into SQL; exported server for input validation tests.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/src/types.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable.
- Tradeoffs: extra prepared statements for counts; scanning source for hygiene instead of runtime checks.
- Notes: injection test ensures bindings; Fastify injected for 400 validation.
```

### CHANGES.md
```md
# C1 — Changes (Run 4)

## Summary
Finalize `host-lite` on top of PR #46 with a unified raw JSON handler path and deterministic responses for `/plan` and `/apply`.

## Why
- Determinism across repeats and environments with canonical JSON bytes and LRU caching.
- Centralized error handling for canonical 400/404 responses.
- Proof tags gated by `DEV_PROOFS` without overhead when off.

## Deltas vs #46
- Unified raw path: added/kept `makeRawHandler(method, url, bodyStr)` delegating to `makeHandler` and wired `createServer` to it.
- Error handling: canonical `400 {"error":"bad_request"}`; `404 {"error":"not_found"}` for non-POST/unknown path.
- Determinism: explicit byte-equality tests for `/plan` and `/apply`.
- LRU: per-world cap fixed at 32; multi-world tests verify no leaks and correct map size.
- Proofs: adopted the "proof-count" gating idea (#48); explicit count check ensures zero entries when off and >0 when on.

## Tests
- Added: `c1.byte-determinism.test.ts`, `c1.proofs-gating-count.test.ts`, `c1.http-400-404.test.ts`, `c1.lru-multiworld.test.ts`, `c1.import-hygiene.test.ts`.
- Determinism/parity: repeated `pnpm -F host-lite-ts test` runs stable; hermetic; no sockets/network.

## Notes
- In-memory only; no new runtime deps; ESM imports include `.js` for internal paths.

# D1 — Changes (Run 1)

## Summary
Claims API now loads legal datasets from SQLite and computes canonical BLAKE3 query hashes. Responses expose dataset version and deterministic evidence samples.

## Why
- Switch from JSON files to SQLite for stable storage.
- Canonical hashing ensures identical queries map to the same `query_hash`.

## Tests
- Added: `services/claims-api-ts/test/sqlite.test.ts`.
- Updated: n/a.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- No schema changes; minimal surface.

# D1 — Changes (Run 2)

## Summary
- Remove committed SQLite DB; switch to in-memory sql.js with schema/seed fixtures.

## Why
- Ensure repo hygiene and deterministic in-memory storage for portable tests.

## Tests
- Updated: services/claims-api-ts/test/sqlite.test.ts.
- Added: packages/d1-sqlite/fixtures/schema.sql; packages/d1-sqlite/fixtures/seed.sql; packages/d1-sqlite/src/db.js.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Queries include ORDER BY for stable row order; evidence sampling yields ≥10 distinct hashes.

# D1 — Changes (Run pass-2)

## Summary
- Harden SQLite adapter with parameterized queries, SQL-based paging, and type-safe DTOs.
- Validate query inputs and expose Fastify instance for testable 400 responses.

## Why
- Ensures deterministic, injection-resistant storage with runtime type checks.

## Tests
- Updated: services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- No schema changes; diffs kept minimal.
```

---

## Run B — PR #55 (50e52bb)
_D1 pass-2: SQLite adapter hardening (param queries, SQL paging, types)_

### REPORT.md
```md
# REPORT — C1 — Run 4

## Goal → Evidence map
- G1 Raw path unified; `createServer` delegates to `makeRawHandler`【F:packages/host-lite/src/server.ts:93】【F:packages/host-lite/src/server.ts:106】
- G2 Endpoints only POST `/plan` and `/apply`; otherwise 404【F:packages/host-lite/src/server.ts:84】【F:packages/host-lite/test/c1.http-400-404.test.ts:6】
- G3 Determinism: `/plan` and `/apply` produce byte-identical responses【F:packages/host-lite/test/c1.byte-determinism.test.ts:7】
- G4 Proof gating: DEV_PROOFS toggles tags; count check【F:packages/host-lite/src/server.ts:58】【F:packages/host-lite/test/c1.proofs-gating-count.test.ts:6】
- G5 LRU bounds: per-world cap 32; map size equals worlds touched【F:packages/host-lite/src/server.ts:9】【F:packages/host-lite/test/c1.lru-multiworld.test.ts:4】
- G6 Hygiene: ESM internal `.js`; public exports only; no deep imports【F:packages/host-lite/test/c1.import-hygiene.test.ts:1】
- G7 Packaging: `main` and `exports` both `src/server.ts`【F:packages/host-lite/package.json:7】

## Notes & tradeoffs
- Centralized parsing simplifies server wiring and ensures canonical error bodies.
- Shared `exec` path guarantees identical planning/apply response shapes and bytes.
- LRU scoped per world prevents cross-world interference and growth.

## Determinism runs
- Repeated `pnpm -F host-lite-ts test` stable across 5 runs (documented in OBS_LOG.md).

# REPORT — D1 — Run 1

## End Goal fulfillment
- EG-1: SQLite adapter serves counts and clauses via CLI-backed queries【F:services/claims-api-ts/src/db.ts†L10-L42】
- EG-2: Responses expose `dataset_version` and BLAKE3 `query_hash` with ≥10 evidence samples【F:services/claims-api-ts/src/db.ts†L37-L41】【F:services/claims-api-ts/src/util.ts†L2-L7】【F:services/claims-api-ts/test/sqlite.test.ts†L34-L45】

## Blockers honored
- B-1: ✅ Storage uses SQLite only (no JSON queries)【F:services/claims-api-ts/src/db.ts†L28-L30】
- B-2: ✅ Identical queries return stable results【F:services/claims-api-ts/test/sqlite.test.ts†L34-L55】

## Lessons / tradeoffs (≤5 bullets)
- Switched from JS libraries to `sqlite3` CLI for deterministic, zero-dep storage.
- Evidence sampling fixed at first 10 ordered rows for stability.
- Canonical JSON hashing guarantees query-key determinism.

## Bench notes (optional, off-mode)
- n/a

# REPORT — D1 — Run 2

## End Goal fulfillment
- EG-1: In-memory sql.js database built from schema/seed fixtures; queries are ordered for determinism【F:packages/d1-sqlite/src/db.js†L1-L15】【F:services/claims-api-ts/src/db.ts†L23-L47】
- EG-2: Responses expose dataset version and BLAKE3 `query_hash` with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L32-L47】【F:services/claims-api-ts/test/sqlite.test.ts†L18-L30】

## Blockers honored
- B-1: ✅ No SQLite binaries tracked; ignore rules added【F:.gitignore†L62-L65】【F:services/claims-api-ts/test/sqlite.test.ts†L6-L10】
- B-2: ✅ Only `sql.js` imported; repeated queries byte-identical【F:services/claims-api-ts/src/server.ts†L1-L43】【F:services/claims-api-ts/test/sqlite.test.ts†L12-L24】

## Lessons / tradeoffs
- Replaced native CLI with WASM `sql.js` for portability.
- Fixture-driven dataset keeps tests hermetic and deterministic.
- Memoized in-memory DB avoids filesystem I/O.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.

# REPORT — D1 — Run 3

## Goal → Evidence map
- G1 SQLite engine uses in-memory sql.js fixtures with parameterized queries and ORDER BY/LIMIT/OFFSET for determinism【F:packages/d1-sqlite/src/db.js†L1-L17】【F:services/claims-api-ts/src/db.ts†L22-L77】
- G2 Responses include dataset version and BLAKE3 query hashes【F:services/claims-api-ts/src/db.ts†L60-L63】【F:services/claims-api-ts/src/util.ts†L2-L8】
- G3 Input validation and parameterized SQL prevent injection, returning 400 on bad shapes【F:services/claims-api-ts/src/server.ts†L7-L33】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L70】
- G4 Paging performed in SQL with deterministic slices across runs【F:services/claims-api-ts/src/db.ts†L69-L93】【F:services/claims-api-ts/test/sqlite.test.ts†L21-L33】

## Notes & tradeoffs
- Evidence deduped by hash to ensure ≥10 distinct samples.
- Fastify builder exposes hermetic server for tests without network sockets.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 4

## Blockers (must all be ✅)
- [x] No kernel/schema changes — code link: packages/host-lite/src/server.ts
- [x] No per-call locks or `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports include `.js` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Tests parallel-safe, no global bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Deterministic canonical outputs — code/test link: packages/host-lite/src/server.ts
- [x] In-memory host only `/plan` & `/apply` — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proofs gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Per-world LRU cache cap 32 — code/test link: packages/host-lite/src/server.ts
- [x] No new runtime dependencies — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/network) — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No new runtime deps — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/fs/network side-effects) — test link: packages/host-lite/test/c1.http-400-404.test.ts
- [x] Public-exports only (no deep relative imports) — test link: packages/host-lite/test/c1.import-hygiene.test.ts
- [x] Do not edit `.codex/tasks/**` — n/a
- [x] Package exports remain `src/server.ts` — code link: packages/host-lite/package.json

## Acceptance (oracle)
- [x] Enable/disable behavior
- [x] Cache cold→warm; reset forces re-read
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (ESM)
- [x] Code quality (minimal diff)
- [x] 404/400 canonical errors — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Multi-world cache bound proof — test link: packages/host-lite/tests/host-lite.test.ts

## Evidence
- Code: packages/host-lite/src/server.ts; packages/host-lite/package.json
- Tests: packages/host-lite/test/c1.byte-determinism.test.ts; packages/host-lite/test/c1.proofs-gating-count.test.ts; packages/host-lite/test/c1.http-400-404.test.ts; packages/host-lite/test/c1.lru-multiworld.test.ts; packages/host-lite/test/c1.import-hygiene.test.ts
- Runs: `pnpm -F host-lite-ts test`
- Bench (off-mode, if applicable): n/a

# COMPLIANCE — D1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks or `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js` — code link: services/claims-api-ts/src/server.ts
- [x] Tests parallel-safe, deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage strictly SQLite — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Identical queries stable; ≥10 evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Storage via SQLite only
- [x] Hashes/versions match expected
- [x] Stability across identical queries
- [x] ≥10 evidence samples per response
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts
- Tests: services/claims-api-ts/test/sqlite.test.ts
- CI runs: `pnpm --filter claims-api-ts test`
- Bench: n/a

# COMPLIANCE — D1 — Run 2

## Blockers (must all be ✅)
- [x] Remove repo-tracked DB; ignore SQLite artifacts — code link: .gitignore
- [x] Storage via in-memory sql.js builder with fixtures — code link: packages/d1-sqlite/src/db.js
- [x] All queries ORDER BY; no `as any`; ≥10 evidence — code link: services/claims-api-ts/src/db.ts
- [x] Responses expose dataset version and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Tests hermetic; no binaries tracked — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] `git ls-files` returns no `.db` or `.sqlite` files
- [x] Stability across identical queries
- [x] ≥10 evidence samples per count response
- [x] Storage proof: only `sql.js` imported
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 3

## Blockers (must all be ✅)
- [x] SQLite via in-memory sql.js builder from fixtures — code link: packages/d1-sqlite/src/db.js
- [x] No committed DB binaries; ignore rules present — code link: .gitignore
- [x] All queries parameterized with ORDER BY/LIMIT/OFFSET — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] ≥10 distinct evidence samples per response — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-2)
- [x] No JS paging; SQL `LIMIT/OFFSET` only — code/test link: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] Parameterized SQL only; injection test — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Input validation returns 400 for bad shapes — code/test link: services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] No `as any`; typed DTOs — code link: services/claims-api-ts/src/types.ts; services/claims-api-ts/src/db.ts
- [x] ESM imports include `.js`; no deep cross-package imports — code/test link: services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Injection-shaped value yields safe result
- [x] Paging stable across runs
- [x] Deterministic responses across repeats
- [x] ≥10 evidence samples per count response
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/src/types.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run 3

- Strategy: harden SQLite adapter with parameterized queries and SQL-level paging; expose Fastify builder for hermetic tests.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism runs: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: added simple manual validation instead of heavier schema library; kept dataset small for fixture loading.
- Notes: ensured injection attempts return safe empty results; no JS slicing or `as any`.
```

### CHANGES.md
```md
# C1 — Changes (Run 4)

## Summary
Finalize `host-lite` on top of PR #46 with a unified raw JSON handler path and deterministic responses for `/plan` and `/apply`.

## Why
- Determinism across repeats and environments with canonical JSON bytes and LRU caching.
- Centralized error handling for canonical 400/404 responses.
- Proof tags gated by `DEV_PROOFS` without overhead when off.

## Deltas vs #46
- Unified raw path: added/kept `makeRawHandler(method, url, bodyStr)` delegating to `makeHandler` and wired `createServer` to it.
- Error handling: canonical `400 {"error":"bad_request"}`; `404 {"error":"not_found"}` for non-POST/unknown path.
- Determinism: explicit byte-equality tests for `/plan` and `/apply`.
- LRU: per-world cap fixed at 32; multi-world tests verify no leaks and correct map size.
- Proofs: adopted the "proof-count" gating idea (#48); explicit count check ensures zero entries when off and >0 when on.

## Tests
- Added: `c1.byte-determinism.test.ts`, `c1.proofs-gating-count.test.ts`, `c1.http-400-404.test.ts`, `c1.lru-multiworld.test.ts`, `c1.import-hygiene.test.ts`.
- Determinism/parity: repeated `pnpm -F host-lite-ts test` runs stable; hermetic; no sockets/network.

## Notes
- In-memory only; no new runtime deps; ESM imports include `.js` for internal paths.

# D1 — Changes (Run 1)

## Summary
Claims API now loads legal datasets from SQLite and computes canonical BLAKE3 query hashes. Responses expose dataset version and deterministic evidence samples.

## Why
- Switch from JSON files to SQLite for stable storage.
- Canonical hashing ensures identical queries map to the same `query_hash`.

## Tests
- Added: `services/claims-api-ts/test/sqlite.test.ts`.
- Updated: n/a.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- No schema changes; minimal surface.

# D1 — Changes (Run 2)

## Summary
- Remove committed SQLite DB; switch to in-memory sql.js with schema/seed fixtures.

## Why
- Ensure repo hygiene and deterministic in-memory storage for portable tests.

## Tests
- Updated: services/claims-api-ts/test/sqlite.test.ts.
- Added: packages/d1-sqlite/fixtures/schema.sql; packages/d1-sqlite/fixtures/seed.sql; packages/d1-sqlite/src/db.js.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Queries include ORDER BY for stable row order; evidence sampling yields ≥10 distinct hashes.

# D1 — Changes (Run 3)

## Summary
Parameterized the SQLite adapter and API layer, adding SQL-level paging, input validation, and typed DTOs for deterministic and injection-safe responses.

## Why
- Ensures all user queries are bound parameters with explicit ORDER BY/LIMIT/OFFSET for deterministic results.
- Guards against SQL injection and invalid query shapes while keeping storage in-memory via sql.js fixtures.

## Tests
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- No schema changes.
- Diffs kept minimal.
```

---

## Run C — PR #56 (a2f0776)
_D1 pass-2: SQLite adapter hardening (param queries, SQL paging, types)_

### REPORT.md
```md
# REPORT — C1 — Run 4

## Goal → Evidence map
- G1 Raw path unified; `createServer` delegates to `makeRawHandler`【F:packages/host-lite/src/server.ts:93】【F:packages/host-lite/src/server.ts:106】
- G2 Endpoints only POST `/plan` and `/apply`; otherwise 404【F:packages/host-lite/src/server.ts:84】【F:packages/host-lite/test/c1.http-400-404.test.ts:6】
- G3 Determinism: `/plan` and `/apply` produce byte-identical responses【F:packages/host-lite/test/c1.byte-determinism.test.ts:7】
- G4 Proof gating: DEV_PROOFS toggles tags; count check【F:packages/host-lite/src/server.ts:58】【F:packages/host-lite/test/c1.proofs-gating-count.test.ts:6】
- G5 LRU bounds: per-world cap 32; map size equals worlds touched【F:packages/host-lite/src/server.ts:9】【F:packages/host-lite/test/c1.lru-multiworld.test.ts:4】
- G6 Hygiene: ESM internal `.js`; public exports only; no deep imports【F:packages/host-lite/test/c1.import-hygiene.test.ts:1】
- G7 Packaging: `main` and `exports` both `src/server.ts`【F:packages/host-lite/package.json:7】

## Notes & tradeoffs
- Centralized parsing simplifies server wiring and ensures canonical error bodies.
- Shared `exec` path guarantees identical planning/apply response shapes and bytes.
- LRU scoped per world prevents cross-world interference and growth.

## Determinism runs
- Repeated `pnpm -F host-lite-ts test` stable across 5 runs (documented in OBS_LOG.md).

# REPORT — D1 — Run 1

## End Goal fulfillment
- EG-1: SQLite adapter serves counts and clauses via CLI-backed queries【F:services/claims-api-ts/src/db.ts†L10-L42】
- EG-2: Responses expose `dataset_version` and BLAKE3 `query_hash` with ≥10 evidence samples【F:services/claims-api-ts/src/db.ts†L37-L41】【F:services/claims-api-ts/src/util.ts†L2-L7】【F:services/claims-api-ts/test/sqlite.test.ts†L34-L45】

## Blockers honored
- B-1: ✅ Storage uses SQLite only (no JSON queries)【F:services/claims-api-ts/src/db.ts†L28-L30】
- B-2: ✅ Identical queries return stable results【F:services/claims-api-ts/test/sqlite.test.ts†L34-L55】

## Lessons / tradeoffs (≤5 bullets)
- Switched from JS libraries to `sqlite3` CLI for deterministic, zero-dep storage.
- Evidence sampling fixed at first 10 ordered rows for stability.
- Canonical JSON hashing guarantees query-key determinism.

## Bench notes (optional, off-mode)
- n/a

# REPORT — D1 — Run 2

## End Goal fulfillment
- EG-1: In-memory sql.js database built from schema/seed fixtures; queries are ordered for determinism【F:packages/d1-sqlite/src/db.js†L1-L15】【F:services/claims-api-ts/src/db.ts†L23-L47】
- EG-2: Responses expose dataset version and BLAKE3 `query_hash` with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L32-L47】【F:services/claims-api-ts/test/sqlite.test.ts†L18-L30】

## Blockers honored
- B-1: ✅ No SQLite binaries tracked; ignore rules added【F:.gitignore†L62-L65】【F:services/claims-api-ts/test/sqlite.test.ts†L6-L10】
- B-2: ✅ Only `sql.js` imported; repeated queries byte-identical【F:services/claims-api-ts/src/server.ts†L1-L43】【F:services/claims-api-ts/test/sqlite.test.ts†L12-L24】

## Lessons / tradeoffs
- Replaced native CLI with WASM `sql.js` for portability.
- Fixture-driven dataset keeps tests hermetic and deterministic.
- Memoized in-memory DB avoids filesystem I/O.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.

# REPORT — D1 — Run 3

## End Goal fulfillment
- G1: SQLite engine via sql.js fixtures; parameterized queries with ORDER BY for determinism【F:services/claims-api-ts/src/db.ts†L23-L78】
- G2: Responses include dataset_version and canonical BLAKE3 query_hash【F:services/claims-api-ts/src/db.ts†L55-L76】【F:services/claims-api-ts/src/util.ts†L2-L7】
- G3: SQL paging/filtering through LIMIT/OFFSET; no JS slicing【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L28-L39】
- G4: Input validation with 400 errors for invalid shapes【F:services/claims-api-ts/src/filters.ts†L3-L30】【F:services/claims-api-ts/src/app.ts†L21-L42】
- G5: Injection-shaped values treated as data, not SQL【F:services/claims-api-ts/test/sqlite.test.ts†L64-L68】

## Blockers honored
- B-1: No DB binaries tracked; `.gitignore` forbids them【F:.gitignore†L62-L65】
- B-2: ESM imports include `.js`; no deep package imports【F:services/claims-api-ts/test/sqlite.test.ts†L50-L63】
- B-3: Tests hermetic and deterministic【F:services/claims-api-ts/test/sqlite.test.ts†L1-L69】

## Lessons / tradeoffs
- Manual filter validator avoids adding schema deps while ensuring type safety.
- Using SQL LIMIT/OFFSET keeps memory use predictable and enforces ordering.
- Parameterized statements cover all user input, blocking injection.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 4

## Blockers (must all be ✅)
- [x] No kernel/schema changes — code link: packages/host-lite/src/server.ts
- [x] No per-call locks or `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports include `.js` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Tests parallel-safe, no global bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Deterministic canonical outputs — code/test link: packages/host-lite/src/server.ts
- [x] In-memory host only `/plan` & `/apply` — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proofs gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Per-world LRU cache cap 32 — code/test link: packages/host-lite/src/server.ts
- [x] No new runtime dependencies — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/network) — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No new runtime deps — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/fs/network side-effects) — test link: packages/host-lite/test/c1.http-400-404.test.ts
- [x] Public-exports only (no deep relative imports) — test link: packages/host-lite/test/c1.import-hygiene.test.ts
- [x] Do not edit `.codex/tasks/**` — n/a
- [x] Package exports remain `src/server.ts` — code link: packages/host-lite/package.json

## Acceptance (oracle)
- [x] Enable/disable behavior
- [x] Cache cold→warm; reset forces re-read
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (ESM)
- [x] Code quality (minimal diff)
- [x] 404/400 canonical errors — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Multi-world cache bound proof — test link: packages/host-lite/tests/host-lite.test.ts

## Evidence
- Code: packages/host-lite/src/server.ts; packages/host-lite/package.json
- Tests: packages/host-lite/test/c1.byte-determinism.test.ts; packages/host-lite/test/c1.proofs-gating-count.test.ts; packages/host-lite/test/c1.http-400-404.test.ts; packages/host-lite/test/c1.lru-multiworld.test.ts; packages/host-lite/test/c1.import-hygiene.test.ts
- Runs: `pnpm -F host-lite-ts test`
- Bench (off-mode, if applicable): n/a

# COMPLIANCE — D1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks or `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js` — code link: services/claims-api-ts/src/server.ts
- [x] Tests parallel-safe, deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage strictly SQLite — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Identical queries stable; ≥10 evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Storage via SQLite only
- [x] Hashes/versions match expected
- [x] Stability across identical queries
- [x] ≥10 evidence samples per response
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts
- Tests: services/claims-api-ts/test/sqlite.test.ts
- CI runs: `pnpm --filter claims-api-ts test`
- Bench: n/a

# COMPLIANCE — D1 — Run 2

## Blockers (must all be ✅)
- [x] Remove repo-tracked DB; ignore SQLite artifacts — code link: .gitignore
- [x] Storage via in-memory sql.js builder with fixtures — code link: packages/d1-sqlite/src/db.js
- [x] All queries ORDER BY; no `as any`; ≥10 evidence — code link: services/claims-api-ts/src/db.ts
- [x] Responses expose dataset version and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Tests hermetic; no binaries tracked — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] `git ls-files` returns no `.db` or `.sqlite` files
- [x] Stability across identical queries
- [x] ≥10 evidence samples per count response
- [x] Storage proof: only `sql.js` imported
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 3

## Blockers (must all be ✅)
- [x] In-memory sql.js builder with fixtures — code link: packages/d1-sqlite/src/db.js
- [x] Parameterized SQL with `WHERE` + `LIMIT/OFFSET`; no JS slice — code link: services/claims-api-ts/src/db.ts
- [x] Deterministic ORDER BY and canonical BLAKE3 hashing — code link: services/claims-api-ts/src/db.ts
- [x] Input validation; 400 on invalid shapes — code link: services/claims-api-ts/src/filters.ts; test link: services/claims-api-ts/test/sqlite.test.ts
- [x] No `as any`; typed DTOs — code link: services/claims-api-ts/src/types.ts
- [x] Injection-shaped value treated as plain string — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ESM internal imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & parallel-safe — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] .gitignore blocks `.db`/`.sqlite*` — code link: .gitignore

## EXTRA BLOCKERS (pass-2)
- Parameterized SQL only; injection test present.
- SQL paging/filtering; no JS slicing.
- Input validation with 400 responses.
- Hygiene scan for `.js` internal imports and absence of deep imports.

## Acceptance (oracle)
- [x] Injection value `' OR 1=1 --` yields no leakage — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Paging `limit/offset` stable across runs — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Determinism loop: repeated queries byte-identical — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; services/claims-api-ts/src/types.ts; packages/d1-sqlite/src/db.js; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run 3

- Strategy: parameterize SQL queries and move paging to LIMIT/OFFSET; add filter validation.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — byte-identical outputs.
- Tradeoffs: added simple manual validation to avoid extra deps; reused sql.js builder for hermetic tests.
- Notes: grep checks ensure no JS slicing or deep imports.
```

### CHANGES.md
```md
# C1 — Changes (Run 4)

## Summary
Finalize `host-lite` on top of PR #46 with a unified raw JSON handler path and deterministic responses for `/plan` and `/apply`.

## Why
- Determinism across repeats and environments with canonical JSON bytes and LRU caching.
- Centralized error handling for canonical 400/404 responses.
- Proof tags gated by `DEV_PROOFS` without overhead when off.

## Deltas vs #46
- Unified raw path: added/kept `makeRawHandler(method, url, bodyStr)` delegating to `makeHandler` and wired `createServer` to it.
- Error handling: canonical `400 {"error":"bad_request"}`; `404 {"error":"not_found"}` for non-POST/unknown path.
- Determinism: explicit byte-equality tests for `/plan` and `/apply`.
- LRU: per-world cap fixed at 32; multi-world tests verify no leaks and correct map size.
- Proofs: adopted the "proof-count" gating idea (#48); explicit count check ensures zero entries when off and >0 when on.

## Tests
- Added: `c1.byte-determinism.test.ts`, `c1.proofs-gating-count.test.ts`, `c1.http-400-404.test.ts`, `c1.lru-multiworld.test.ts`, `c1.import-hygiene.test.ts`.
- Determinism/parity: repeated `pnpm -F host-lite-ts test` runs stable; hermetic; no sockets/network.

## Notes
- In-memory only; no new runtime deps; ESM imports include `.js` for internal paths.

# D1 — Changes (Run 1)

## Summary
Claims API now loads legal datasets from SQLite and computes canonical BLAKE3 query hashes. Responses expose dataset version and deterministic evidence samples.

## Why
- Switch from JSON files to SQLite for stable storage.
- Canonical hashing ensures identical queries map to the same `query_hash`.

## Tests
- Added: `services/claims-api-ts/test/sqlite.test.ts`.
- Updated: n/a.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- No schema changes; minimal surface.

# D1 — Changes (Run 2)

## Summary
- Remove committed SQLite DB; switch to in-memory sql.js with schema/seed fixtures.

## Why
- Ensure repo hygiene and deterministic in-memory storage for portable tests.

## Tests
- Updated: services/claims-api-ts/test/sqlite.test.ts.
- Added: packages/d1-sqlite/fixtures/schema.sql; packages/d1-sqlite/fixtures/seed.sql; packages/d1-sqlite/src/db.js.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Queries include ORDER BY for stable row order; evidence sampling yields ≥10 distinct hashes.

# D1 — Changes (Run 3)

## Summary
- Harden SQLite adapter with parameterized queries and SQL-driven paging.
- Validate request filters and expose typed DTOs; reject malformed input with 400.

## Why
- Prevent SQL injection and ensure deterministic slices without loading whole tables.
- Improve type safety and API correctness compared to pass-1 (#53).

## Tests
- Updated: services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- LIMIT/OFFSET enforced in SQL only; queries use placeholders for all parameters.
```

---

## Run D — PR #57 (5d9a5c5)
_D1 pass-2: SQLite adapter hardening (param queries, SQL paging, types)_

### REPORT.md
```md
# REPORT — C1 — Run 4

## Goal → Evidence map
- G1 Raw path unified; `createServer` delegates to `makeRawHandler`【F:packages/host-lite/src/server.ts:93】【F:packages/host-lite/src/server.ts:106】
- G2 Endpoints only POST `/plan` and `/apply`; otherwise 404【F:packages/host-lite/src/server.ts:84】【F:packages/host-lite/test/c1.http-400-404.test.ts:6】
- G3 Determinism: `/plan` and `/apply` produce byte-identical responses【F:packages/host-lite/test/c1.byte-determinism.test.ts:7】
- G4 Proof gating: DEV_PROOFS toggles tags; count check【F:packages/host-lite/src/server.ts:58】【F:packages/host-lite/test/c1.proofs-gating-count.test.ts:6】
- G5 LRU bounds: per-world cap 32; map size equals worlds touched【F:packages/host-lite/src/server.ts:9】【F:packages/host-lite/test/c1.lru-multiworld.test.ts:4】
- G6 Hygiene: ESM internal `.js`; public exports only; no deep imports【F:packages/host-lite/test/c1.import-hygiene.test.ts:1】
- G7 Packaging: `main` and `exports` both `src/server.ts`【F:packages/host-lite/package.json:7】

## Notes & tradeoffs
- Centralized parsing simplifies server wiring and ensures canonical error bodies.
- Shared `exec` path guarantees identical planning/apply response shapes and bytes.
- LRU scoped per world prevents cross-world interference and growth.

## Determinism runs
- Repeated `pnpm -F host-lite-ts test` stable across 5 runs (documented in OBS_LOG.md).

# REPORT — D1 — Run 1

## End Goal fulfillment
- EG-1: SQLite adapter serves counts and clauses via CLI-backed queries【F:services/claims-api-ts/src/db.ts†L10-L42】
- EG-2: Responses expose `dataset_version` and BLAKE3 `query_hash` with ≥10 evidence samples【F:services/claims-api-ts/src/db.ts†L37-L41】【F:services/claims-api-ts/src/util.ts†L2-L7】【F:services/claims-api-ts/test/sqlite.test.ts†L34-L45】

## Blockers honored
- B-1: ✅ Storage uses SQLite only (no JSON queries)【F:services/claims-api-ts/src/db.ts†L28-L30】
- B-2: ✅ Identical queries return stable results【F:services/claims-api-ts/test/sqlite.test.ts†L34-L55】

## Lessons / tradeoffs (≤5 bullets)
- Switched from JS libraries to `sqlite3` CLI for deterministic, zero-dep storage.
- Evidence sampling fixed at first 10 ordered rows for stability.
- Canonical JSON hashing guarantees query-key determinism.

## Bench notes (optional, off-mode)
- n/a

# REPORT — D1 — Run 2

## End Goal fulfillment
- EG-1: In-memory sql.js database built from schema/seed fixtures; queries are ordered for determinism【F:packages/d1-sqlite/src/db.js†L1-L15】【F:services/claims-api-ts/src/db.ts†L23-L47】
- EG-2: Responses expose dataset version and BLAKE3 `query_hash` with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L32-L47】【F:services/claims-api-ts/test/sqlite.test.ts†L18-L30】

## Blockers honored
- B-1: ✅ No SQLite binaries tracked; ignore rules added【F:.gitignore†L62-L65】【F:services/claims-api-ts/test/sqlite.test.ts†L6-L10】
- B-2: ✅ Only `sql.js` imported; repeated queries byte-identical【F:services/claims-api-ts/src/server.ts†L1-L43】【F:services/claims-api-ts/test/sqlite.test.ts†L12-L24】

## Lessons / tradeoffs
- Replaced native CLI with WASM `sql.js` for portability.
- Fixture-driven dataset keeps tests hermetic and deterministic.
- Memoized in-memory DB avoids filesystem I/O.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.

# REPORT — D1 — Run 3

## End Goal fulfillment
- EG-1: SQLite adapter uses parameterized queries with SQL paging and returns typed rows【F:services/claims-api-ts/src/db.ts†L24-L86】【F:services/claims-api-ts/src/db.ts†L88-L124】
- EG-2: Responses include dataset version and BLAKE3 `query_hash` with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L65-L86】【F:services/claims-api-ts/test/sqlite.test.ts†L27-L39】

## Blockers honored
- B-1: ✅ No `as any`; inputs validated and 400 on invalid shapes【F:services/claims-api-ts/src/server.ts†L23-L48】【F:services/claims-api-ts/src/server.ts†L50-L59】
- B-2: ✅ SQL paging; no JS slicing【F:services/claims-api-ts/src/db.ts†L88-L104】【F:services/claims-api-ts/test/sqlite.test.ts†L41-L55】
- B-3: ✅ Parameterized SQL only; injection attempt neutralized【F:services/claims-api-ts/src/db.ts†L40-L47】【F:services/claims-api-ts/test/sqlite.test.ts†L18-L25】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statements with bound parameters guard against injection.
- Input validation adds minimal branching but ensures type safety.
- SQL LIMIT/OFFSET keeps paging deterministic and avoids JS memory overhead.

## Determinism runs
- `pnpm --filter claims-api-ts test` and `pnpm test` repeated 3× — stable.
```

### COMPLIANCE.md
```md
# COMPLIANCE — C1 — Run 4

## Blockers (must all be ✅)
- [x] No kernel/schema changes — code link: packages/host-lite/src/server.ts
- [x] No per-call locks or `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports include `.js` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Tests parallel-safe, no global bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Deterministic canonical outputs — code/test link: packages/host-lite/src/server.ts
- [x] In-memory host only `/plan` & `/apply` — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proofs gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Per-world LRU cache cap 32 — code/test link: packages/host-lite/src/server.ts
- [x] No new runtime dependencies — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/network) — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No new runtime deps — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/fs/network side-effects) — test link: packages/host-lite/test/c1.http-400-404.test.ts
- [x] Public-exports only (no deep relative imports) — test link: packages/host-lite/test/c1.import-hygiene.test.ts
- [x] Do not edit `.codex/tasks/**` — n/a
- [x] Package exports remain `src/server.ts` — code link: packages/host-lite/package.json

## Acceptance (oracle)
- [x] Enable/disable behavior
- [x] Cache cold→warm; reset forces re-read
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (ESM)
- [x] Code quality (minimal diff)
- [x] 404/400 canonical errors — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Multi-world cache bound proof — test link: packages/host-lite/tests/host-lite.test.ts

## Evidence
- Code: packages/host-lite/src/server.ts; packages/host-lite/package.json
- Tests: packages/host-lite/test/c1.byte-determinism.test.ts; packages/host-lite/test/c1.proofs-gating-count.test.ts; packages/host-lite/test/c1.http-400-404.test.ts; packages/host-lite/test/c1.lru-multiworld.test.ts; packages/host-lite/test/c1.import-hygiene.test.ts
- Runs: `pnpm -F host-lite-ts test`
- Bench (off-mode, if applicable): n/a

# COMPLIANCE — D1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks or `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js` — code link: services/claims-api-ts/src/server.ts
- [x] Tests parallel-safe, deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage strictly SQLite — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Identical queries stable; ≥10 evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Storage via SQLite only
- [x] Hashes/versions match expected
- [x] Stability across identical queries
- [x] ≥10 evidence samples per response
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts
- Tests: services/claims-api-ts/test/sqlite.test.ts
- CI runs: `pnpm --filter claims-api-ts test`
- Bench: n/a

# COMPLIANCE — D1 — Run 2

## Blockers (must all be ✅)
- [x] Remove repo-tracked DB; ignore SQLite artifacts — code link: .gitignore
- [x] Storage via in-memory sql.js builder with fixtures — code link: packages/d1-sqlite/src/db.js
- [x] All queries ORDER BY; no `as any`; ≥10 evidence — code link: services/claims-api-ts/src/db.ts
- [x] Responses expose dataset version and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Tests hermetic; no binaries tracked — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] `git ls-files` returns no `.db` or `.sqlite` files
- [x] Stability across identical queries
- [x] ≥10 evidence samples per count response
- [x] Storage proof: only `sql.js` imported
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 3

## Blockers (must all be ✅)
- [x] No SQL string interpolation; all queries parameterized — code link: services/claims-api-ts/src/db.ts
- [x] SQL paging via LIMIT/OFFSET; no JS slicing — code link: services/claims-api-ts/src/db.ts
- [x] Inputs validated; no `as any`; 400 on invalid shapes — code link: services/claims-api-ts/src/server.ts
- [x] ≥10 distinct evidence samples; deterministic responses — code/test link: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] `.js` internal imports; no deep package paths — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-2)
- [x] No committed DB binaries; `.gitignore` covers SQLite artifacts — code/test link: .gitignore; services/claims-api-ts/test/sqlite.test.ts
- [x] Parameterized SQL only; injection tests — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Paging/filtering done in SQL — code link: services/claims-api-ts/src/db.ts
- [x] Deterministic outputs, ≥10 evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Storage via SQLite only
- [x] Hashes/versions match expected
- [x] Stability across identical queries
- [x] ≥10 evidence samples per response
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`; `pnpm test`
```

### OBS_LOG.md
```md
# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run 3

- Strategy: parameterize all SQL and move paging into LIMIT/OFFSET; add filter validation.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` and `pnpm test` — identical outputs.
- Near-misses: initial tests failed when rg paths were absolute; corrected to package-relative.
- Notes: evidence sampling ensures uniqueness via hash set; no runtime fs/network writes.
```

### CHANGES.md
```md
# C1 — Changes (Run 4)

## Summary
Finalize `host-lite` on top of PR #46 with a unified raw JSON handler path and deterministic responses for `/plan` and `/apply`.

## Why
- Determinism across repeats and environments with canonical JSON bytes and LRU caching.
- Centralized error handling for canonical 400/404 responses.
- Proof tags gated by `DEV_PROOFS` without overhead when off.

## Deltas vs #46
- Unified raw path: added/kept `makeRawHandler(method, url, bodyStr)` delegating to `makeHandler` and wired `createServer` to it.
- Error handling: canonical `400 {"error":"bad_request"}`; `404 {"error":"not_found"}` for non-POST/unknown path.
- Determinism: explicit byte-equality tests for `/plan` and `/apply`.
- LRU: per-world cap fixed at 32; multi-world tests verify no leaks and correct map size.
- Proofs: adopted the "proof-count" gating idea (#48); explicit count check ensures zero entries when off and >0 when on.

## Tests
- Added: `c1.byte-determinism.test.ts`, `c1.proofs-gating-count.test.ts`, `c1.http-400-404.test.ts`, `c1.lru-multiworld.test.ts`, `c1.import-hygiene.test.ts`.
- Determinism/parity: repeated `pnpm -F host-lite-ts test` runs stable; hermetic; no sockets/network.

## Notes
- In-memory only; no new runtime deps; ESM imports include `.js` for internal paths.

# D1 — Changes (Run 1)

## Summary
Claims API now loads legal datasets from SQLite and computes canonical BLAKE3 query hashes. Responses expose dataset version and deterministic evidence samples.

## Why
- Switch from JSON files to SQLite for stable storage.
- Canonical hashing ensures identical queries map to the same `query_hash`.

## Tests
- Added: `services/claims-api-ts/test/sqlite.test.ts`.
- Updated: n/a.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- No schema changes; minimal surface.

# D1 — Changes (Run 2)

## Summary
- Remove committed SQLite DB; switch to in-memory sql.js with schema/seed fixtures.

## Why
- Ensure repo hygiene and deterministic in-memory storage for portable tests.

## Tests
- Updated: services/claims-api-ts/test/sqlite.test.ts.
- Added: packages/d1-sqlite/fixtures/schema.sql; packages/d1-sqlite/fixtures/seed.sql; packages/d1-sqlite/src/db.js.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Queries include ORDER BY for stable row order; evidence sampling yields ≥10 distinct hashes.

# D1 — Changes (Run 3)

## Summary
- Harden SQLite adapter with parameterized queries, SQL LIMIT/OFFSET paging, and typed DTOs.
- Validate request filters and reject malformed or injection-shaped values with 400.

## Why
- Prevent SQL injection and JS-side paging to satisfy pass-2 blockers.
- Ensure deterministic byte-stable responses backed by structured types.

## Tests
- Updated: services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` and `pnpm test` stable.

## Notes
- No schema changes; all filtering/paging in SQL; evidence samples remain ≥10 and distinct.
```
