# Parallel run aggregation
_Winner branch: main — 2025-09-13T05:03:21Z_

---

## Run A — PR #62 (71c89b9)
_D1 pass-4: SQLite adapter — prepared reuse, SQL-only evidence, hardening_

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

# REPORT — D1 — Run 5

## End Goal fulfillment
- EG-1: SQLite adapter built in-memory from fixtures with prepared statement reuse【F:packages/d1-sqlite/src/db.js†L1-L17】【F:services/claims-api-ts/src/db.ts†L1-L78】
- EG-2: Responses return dataset_version and BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L52-L76】【F:services/claims-api-ts/test/sqlite.test.ts†L26-L36】

## Blockers honored
- B-1: ✅ No `as any`; inputs validated【F:services/claims-api-ts/src/filters.ts†L1-L32】
- B-2: ✅ ESM imports include `.js`; no deep imports【F:services/claims-api-ts/test/sqlite.test.ts†L50-L63】

## Lessons / tradeoffs (≤5 bullets)
- Guarded DB initialization yields deterministic 500s without affecting hot paths.
- Allowing limit=0 required filter adjustments but keeps paging logic in SQL.
- Prepared statements proved equivalent to ad-hoc queries, reinforcing reuse.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
- `pnpm test` — workspace tests all pass.

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

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

# COMPLIANCE — D1 — Run 4

## Blockers (must all be ✅)
- [x] Prepared statements reused; no per-call prepares — code link: services/claims-api-ts/src/db.ts
- [x] Evidence samples via SQL DISTINCT/ORDER BY/LIMIT — code link: services/claims-api-ts/src/db.ts
- [x] Parameterized queries; no `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-3)
- [x] No JS pagination/filtering on results — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared statements bound/reset between runs — code link: services/claims-api-ts/src/db.ts
- [x] `.gitignore` covers SQLite binaries — code link: .gitignore
- [x] 400 on invalid shapes (limit=0, offset<0) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage proof: only sql.js imported — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs non-prepared equivalence (stable bytes) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Evidence via SQL only — code link: services/claims-api-ts/src/db.ts
- [x] Paging determinism with large offset — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection test remains green — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 5

## Blockers (must all be ✅)
- [x] No kernel/schema changes — code link: services/claims-api-ts/src/app.ts
- [x] No per-call locks or `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js` — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests parallel-safe, deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage strictly SQLite via sql.js — code link: packages/d1-sqlite/src/db.js
- [x] Responses include `dataset_version` and `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No committed DB binaries; `.gitignore` blocks artifacts — code link: .gitignore
- [x] SQL-only paging/evidence; no `.slice`/`.filter` over rows — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] All queries parameterized; hot paths prepared & reused — code link: services/claims-api-ts/src/db.ts
- [x] No `as any`; inputs validated with 400 on bad shapes — code link: services/claims-api-ts/src/filters.ts

## Acceptance (oracle)
- [x] Prepared vs ad-hoc execution byte-identical — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection-shaped value safe — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Paging boundaries deterministic (limit=0, large offset) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Hygiene scan: .js imports and no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Determinism loop across repeated runs — test link: services/claims-api-ts/test/sqlite.test.ts

## Evidence
- Code: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; packages/d1-sqlite/src/db.js; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`; `pnpm test`
- Bench (off-mode, if applicable): n/a
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

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: guard DB init, add limit=0 path, and compare prepared vs ad-hoc execution.
- Key changes: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: adjusted filter bounds to allow `limit=0` while keeping validation.
- Notes: rg scan expanded to entire src to enforce SQL-only pagination.
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

# D1 — Changes (Run 4)

## Summary
- Reuse prepared SQLite statements and fetch evidence samples purely via SQL.
- Harden paging filters with boundary checks for limit/offset and maintain deterministic bytes.

## Why
- Prepared statement reuse avoids recompilation and keeps responses stable.
- SQL-only evidence and strict filter validation guard against JS-side slicing and malformed inputs.

## Tests
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Grep tests ensure no `.slice(` or `.filter(` over DB rows; large-offset queries return empty pages deterministically.

# D1 — Changes (Run 5)

## Summary
- Guard database initialization to return canonical 500 errors and allow zero-limit paging with deterministic empty slices.
- Prove prepared statements match ad-hoc execution byte-for-byte while enforcing SQL-only evidence and pagination.

## Why
- Ensures resilient startup and keeps responses stable without JS-side filtering.

## Tests
- Updated: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Static scans confirm no `.slice(`/`.filter(` in production code.
```

---

## Run B — PR #63 (57f9376)
_D1 pass-4: SQLite adapter — prepared reuse, SQL-only evidence, hardening_

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

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.

# REPORT — D1 — Run 5

## End Goal fulfillment
- EG-1: SQLite adapter returns dataset version, canonical query_hash, and ≥10 distinct evidences via SQL-only prepared statements【F:services/claims-api-ts/src/db.ts†L58-L90】【F:services/claims-api-ts/test/sqlite.test.ts†L26-L50】
- EG-2: Paging and filters executed in SQL with ORDER BY/LIMIT/OFFSET yielding byte-identical results across runs【F:services/claims-api-ts/src/db.ts†L94-L114】【F:services/claims-api-ts/test/sqlite.test.ts†L37-L61】
- EG-3: Database initialization guarded; failures return deterministic 500 responses【F:services/claims-api-ts/src/app.ts†L5-L66】【F:services/claims-api-ts/test/sqlite.test.ts†L131-L141】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L45-L50】
- B-2: Storage via sql.js only; SQLite artifacts ignored by git【F:packages/d1-sqlite/src/db.js†L1-L17】【F:.gitignore†L62-L70】
- B-3: Inputs validated with typed filters; no `as any` casts【F:services/claims-api-ts/src/filters.ts†L3-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L64-L74】

## Lessons / tradeoffs (≤5 bullets)
- Catching sql.js init errors keeps service responsive but skips retry logic.
- Prepared statement caching assumes single-process use but minimizes compile overhead.
- Grep-based scans are coarse but lightweight for enforcing SQL-only processing.

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

# COMPLIANCE — D1 — Run 4

## Blockers (must all be ✅)
- [x] Prepared statements reused; no per-call prepares — code link: services/claims-api-ts/src/db.ts
- [x] Evidence samples via SQL DISTINCT/ORDER BY/LIMIT — code link: services/claims-api-ts/src/db.ts
- [x] Parameterized queries; no `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-3)
- [x] No JS pagination/filtering on results — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared statements bound/reset between runs — code link: services/claims-api-ts/src/db.ts
- [x] `.gitignore` covers SQLite binaries — code link: .gitignore
- [x] 400 on invalid shapes (limit=0, offset<0) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage proof: only sql.js imported — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs non-prepared equivalence (stable bytes) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Evidence via SQL only — code link: services/claims-api-ts/src/db.ts
- [x] Paging determinism with large offset — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection test remains green — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 5

## Blockers (must all be ✅)
- [x] In-memory sql.js database built from fixtures; no binaries tracked — code link: packages/d1-sqlite/src/db.js; .gitignore
- [x] Parameterized queries with ORDER BY/LIMIT/OFFSET and prepared reuse — code link: services/claims-api-ts/src/db.ts
- [x] Responses include dataset_version and BLAKE3 query_hash — code link: services/claims-api-ts/src/db.ts
- [x] Tests hermetic & deterministic — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No JS pagination/filtering on DB rows — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared vs direct execution yields byte-identical JSON — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] `.gitignore` covers SQLite artifacts — code link: .gitignore
- [x] 500 response when DB init fails — code link: services/claims-api-ts/src/app.ts; test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Injection-shaped values behave as ordinary strings — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples via SQL — code/test link: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] Paging determinism with limit/offset boundaries — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Hygiene scan: internal `.js` imports; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; .gitignore
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

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: handle sql.js init failures and prove prepared statement reuse against ad-hoc queries.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: simple try/catch for DB init; grep scan may not catch dynamic array operations.
- Notes: prepared vs direct execution outputs match exactly; DB failures return canonical 500 error.
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

# D1 — Changes (Run 4)

## Summary
- Reuse prepared SQLite statements and fetch evidence samples purely via SQL.
- Harden paging filters with boundary checks for limit/offset and maintain deterministic bytes.

## Why
- Prepared statement reuse avoids recompilation and keeps responses stable.
- SQL-only evidence and strict filter validation guard against JS-side slicing and malformed inputs.

## Tests
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Grep tests ensure no `.slice(` or `.filter(` over DB rows; large-offset queries return empty pages deterministically.

# D1 — Changes (Run 5)

## Summary
- Guard database initialization and reuse prepared SQLite statements for counts, listings, and evidence, keeping paging and sampling purely in SQL.
- Added coverage for prepared-vs-ad-hoc equivalence and DB startup failures with deterministic 500 responses.

## Why
- Ensures stable outputs even if sql.js fails to load and proves prepared reuse does not alter JSON bytes.

## Tests
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Static scans assert no `.slice(`/`.filter(` over DB rows across sources; error handling returns canonical `{ "error": "db_unavailable" }` with 500 status.
```

---

## Run C — PR #64 (50faf0d)
_D1 pass-4: SQLite adapter — prepared reuse, SQL-only evidence, hardening_

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

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.

# REPORT — D1 — Run 5

## End Goal fulfillment
- EG-1: sql.js in-memory database built from fixtures with prepared statements reused safely; evidence and paging handled entirely in SQL【F:services/claims-api-ts/src/db.ts†L21-L90】【F:services/claims-api-ts/src/app.ts†L7-L59】
- EG-2: Responses carry `dataset_version` and canonical BLAKE3 `query_hash` with ≥10 distinct evidence samples and byte-identical outputs across runs【F:services/claims-api-ts/src/db.ts†L59-L88】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】

## Blockers honored
- B-1: ✅ No JS-side `.slice`/`.filter`; static scans over source【F:services/claims-api-ts/test/sqlite.test.ts†L32-L35】
- B-2: ✅ Prepared, parameterised queries bound/reset; injection value treated as plain string【F:services/claims-api-ts/src/db.ts†L59-L88】【F:services/claims-api-ts/test/sqlite.test.ts†L90-L96】
- B-3: ✅ Safe DB init with deterministic 500 on failure; invalid filter shapes return 400【F:services/claims-api-ts/src/app.ts†L1-L59】【F:services/claims-api-ts/test/init-failure.test.ts†L3-L16】【F:services/claims-api-ts/test/sqlite.test.ts†L64-L78】

## Lessons / tradeoffs (≤5 bullets)
- Guarded initialization avoids crashes but introduces explicit 500 responses when DB is unavailable.
- Verifying prepared vs direct queries ensures optimisation without behavioural change.
- Static scans cover entire service codebase; may miss dynamic string constructions but keeps tooling simple.

## Determinism runs
- 3× `pnpm --filter claims-api-ts test` — all outputs stable.

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

# COMPLIANCE — D1 — Run 4

## Blockers (must all be ✅)
- [x] Prepared statements reused; no per-call prepares — code link: services/claims-api-ts/src/db.ts
- [x] Evidence samples via SQL DISTINCT/ORDER BY/LIMIT — code link: services/claims-api-ts/src/db.ts
- [x] Parameterized queries; no `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-3)
- [x] No JS pagination/filtering on results — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared statements bound/reset between runs — code link: services/claims-api-ts/src/db.ts
- [x] `.gitignore` covers SQLite binaries — code link: .gitignore
- [x] 400 on invalid shapes (limit=0, offset<0) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage proof: only sql.js imported — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs non-prepared equivalence (stable bytes) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Evidence via SQL only — code link: services/claims-api-ts/src/db.ts
- [x] Paging determinism with large offset — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection test remains green — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 5

## Blockers (must all be ✅)
- [x] sql.js in-memory engine with fixtures — code link: packages/d1-sqlite/src/db.js
- [x] ORDER BY on user-visible queries; deterministic JSON — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Parameterised SQL with prepared reuse; ≥10 distinct evidence — code/test link: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] Input validation; 400 for invalid shapes — code/test link: services/claims-api-ts/src/filters.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] No `as any`; type guards ensure narrow casts — code link: services/claims-api-ts/src/db.ts
- [x] Tests hermetic & parallel-safe — test links: services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/test/init-failure.test.ts
- [x] ESM imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] `.gitignore` blocks SQLite artifacts; no DB binaries tracked — code link: .gitignore
- [x] No JS pagination/filtering; static scans reject `.slice`/`.filter` — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared statements bound/reset and reused — code link: services/claims-api-ts/src/db.ts
- [x] Safe DB init yields deterministic 500 on failure — code/test link: services/claims-api-ts/src/app.ts; services/claims-api-ts/test/init-failure.test.ts
- [x] Deterministic 400 responses for invalid shapes — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs direct execution byte-identical — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Determinism loop stable across runs — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection-shaped value handled safely — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Paging boundaries (`limit=0`, large `offset`) deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Hygiene scan: internal imports end with `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM) — code link: services/claims-api-ts/package.json
- [x] Code quality — code link: services/claims-api-ts/src/db.ts

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; packages/d1-sqlite/src/db.js; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/test/init-failure.test.ts
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

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: add guarded DB initialization and verify prepared statements against direct execution while tightening type checks.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/test/init-failure.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — all byte-identical.
- Near-misses vs blockers: mocking openDb to fail required module reset to avoid cross-test leakage.
- Notes: static scans now cover entire service source to ensure no JS slicing/filtering.
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

# D1 — Changes (Run 4)

## Summary
- Reuse prepared SQLite statements and fetch evidence samples purely via SQL.
- Harden paging filters with boundary checks for limit/offset and maintain deterministic bytes.

## Why
- Prepared statement reuse avoids recompilation and keeps responses stable.
- SQL-only evidence and strict filter validation guard against JS-side slicing and malformed inputs.

## Tests
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Grep tests ensure no `.slice(` or `.filter(` over DB rows; large-offset queries return empty pages deterministically.

# D1 — Changes (Run 5)

## Summary
Guarded the SQLite adapter with safe initialization and type narrowing while proving that prepared statements return the same JSON as direct execution.

## Why
Ensures deterministic failure modes and validates prepared reuse without altering response bytes.

## Tests
- Added: services/claims-api-ts/test/init-failure.test.ts.
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- No schema changes; static scans confirm absence of JS-side slicing/filtering.
```

---

## Run D — PR #65 (c7daa98)
_D1 pass-4: SQLite adapter — prepared reuse, SQL-only evidence, hardening_

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

# REPORT — D1 — Run 5

## End Goal fulfillment
- G1: Guarded sql.js initialization builds in-memory DB from fixtures with canonical failure path【F:services/claims-api-ts/src/db.ts†L22-L47】【F:services/claims-api-ts/src/app.ts†L5-L13】
- G2: Responses carry dataset version and BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L66-L82】【F:services/claims-api-ts/test/sqlite.test.ts†L26-L35】
- G3: SQL-only paging/evidence; prepared reuse matches fresh statements【F:services/claims-api-ts/src/db.ts†L39-L45】【F:services/claims-api-ts/test/sqlite.test.ts†L37-L51】【F:services/claims-api-ts/test/sqlite.test.ts†L63-L94】
- G4: Invalid filters return deterministic 400s; DB init failures yield 500【F:services/claims-api-ts/src/app.ts†L5-L13】【F:services/claims-api-ts/test/sqlite.test.ts†L97-L111】【F:services/claims-api-ts/test/sqlite.test.ts†L137-L144】

## Blockers honored
- B-1: No JS slicing/filtering; grep over src ensures none【F:services/claims-api-ts/test/sqlite.test.ts†L37-L51】
- B-2: Parameterized, prepared statements reused and reset【F:services/claims-api-ts/src/db.ts†L22-L45】
- B-3: `.gitignore` forbids SQLite artifacts【F:.gitignore†L62-L65】
- B-4: Tests hermetic and deterministic【F:services/claims-api-ts/test/sqlite.test.ts†L1-L145】

## Lessons / tradeoffs (≤5 bullets)
- Mock-based init failure test requires module cache resets but ensures deterministic 500s.
- Prepared statement caching keeps byte-identical responses without per-call compilation.
- Repository-wide regex guard prevents accidental JS paging/filtering.
- Metadata checks abort early if dataset_version missing.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

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

# COMPLIANCE — D1 — Run 4

## Blockers (must all be ✅)
- [x] Prepared statements reused; no per-call prepares — code link: services/claims-api-ts/src/db.ts
- [x] Evidence samples via SQL DISTINCT/ORDER BY/LIMIT — code link: services/claims-api-ts/src/db.ts
- [x] Parameterized queries; no `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-3)
- [x] No JS pagination/filtering on results — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared statements bound/reset between runs — code link: services/claims-api-ts/src/db.ts
- [x] `.gitignore` covers SQLite binaries — code link: .gitignore
- [x] 400 on invalid shapes (limit=0, offset<0) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage proof: only sql.js imported — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs non-prepared equivalence (stable bytes) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Evidence via SQL only — code link: services/claims-api-ts/src/db.ts
- [x] Paging determinism with large offset — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection test remains green — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 5

## Blockers (must all be ✅)
- [x] sql.js in-memory builder with fixtures; no DB binaries tracked — code link: packages/d1-sqlite/src/db.js; `.gitignore`
- [x] Parameterized queries with ORDER BY; statements prepared & reused — code link: services/claims-api-ts/src/db.ts
- [x] Responses include `dataset_version` and BLAKE3 `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] Input validation with 400s; DB init failure returns 500 — code link: services/claims-api-ts/src/app.ts; test link: services/claims-api-ts/test/sqlite.test.ts
- [x] No `as any`; typed DTOs — code link: services/claims-api-ts/src/types.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared vs fresh equivalence; no `.slice`/`.filter` — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ESM imports end with `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & deterministic — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No JS pagination/filtering on user-visible data — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared statements bound/reset between calls — code link: services/claims-api-ts/src/db.ts
- [x] `.gitignore` covers SQLite artifacts — code link: .gitignore
- [x] 400 for invalid shapes and deterministic 500 on init failure — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage proof: only sql.js imported — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs non-prepared equivalence — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] SQL-only evidence and paging; grep ensures no `.slice`/`.filter` — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection value `' OR 1=1 --` yields no leakage — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Paging boundaries deterministic across runs — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; packages/d1-sqlite/src/db.js; .gitignore
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

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: guard DB init and assert prepared reuse equals fresh execution; widen grep scans for SQL-only paging.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: mock-based init failure test introduces module resets but keeps external API unchanged.
- Notes: deterministic 400/500 JSON and repository-wide `.slice`/`.filter` guard.
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

# D1 — Changes (Run 4)

## Summary
- Reuse prepared SQLite statements and fetch evidence samples purely via SQL.
- Harden paging filters with boundary checks for limit/offset and maintain deterministic bytes.

## Why
- Prepared statement reuse avoids recompilation and keeps responses stable.
- SQL-only evidence and strict filter validation guard against JS-side slicing and malformed inputs.

## Tests
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Grep tests ensure no `.slice(` or `.filter(` over DB rows; large-offset queries return empty pages deterministically.

# D1 — Changes (Run 5)

## Summary
- Guard database initialization and return canonical 500 errors when sql.js fails.
- Enforce SQL-only paging and evidence with prepared-statement reuse verified against fresh executions.

## Why
- Defensive init keeps service responses deterministic even when the engine is unavailable.
- Prepared reuse and SQL scans prove there is no JS-side slicing or filtering.

## Tests
- Updated: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism/parity: repeated `pnpm --filter claims-api-ts test` stable.

## Notes
- Invalid filters and DB failures yield byte-identical 400/500 JSON across runs.
```
