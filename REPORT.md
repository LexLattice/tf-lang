# REPORT — E2 — Run 1

## End Goal fulfillment
- EG-1: Proof tags render from dataset data in sorted order, enabling deterministic DOM across sources【F:docs/claims-explorer.html†L206-L219】【F:packages/explorer-test/claims-explorer.test.ts†L82-L105】
- EG-2: When datasets lack tags the tags panel stays hidden in both static and API modes【F:packages/explorer-test/claims-explorer.test.ts†L128-L136】
- EG-3: Static and API renders produce byte-identical DOM snapshots when tags exist【F:packages/explorer-test/claims-explorer.test.ts†L82-L105】

## Blockers honored
- B-1: ✅ No per-call locks or `as any`【F:docs/claims-explorer.html†L206-L219】
- B-2: ✅ ESM internal imports use `.js`【F:packages/explorer-test/claims-explorer.test.ts†L1-L3】
- B-3: ✅ Tags rendered only from dataset/meta data【F:docs/claims-explorer.html†L206-L219】
- B-4: ✅ Tags panel hidden when no tags【F:packages/explorer-test/claims-explorer.test.ts†L128-L136】
- B-5: ✅ Rendering order stable via sort【F:docs/claims-explorer.html†L206-L219】

## Lessons / tradeoffs (≤5 bullets)
- Sorting at render time guards against inconsistent upstream tag order.
- JSDOM tests verify deterministic cross-source behavior without network access.

## Bench notes (optional, off-mode)
- n/a

# REPORT — E1 — Run 2

## End Goal fulfillment
- EG-1: `/health` provides dataset version, tags and default date for API mode; static mode draws tags from dataset metadata【F:docs/claims-explorer.html†L143-L148】【F:docs/claims-explorer.html†L277-L304】
- EG-2: Default date auto-selects from `at` or `generated_at`; tags panel hidden when no tags and rendered with sorted tags when present【F:docs/claims-explorer.html†L291-L313】【F:docs/claims-explorer.html†L180-L195】【F:packages/explorer-test/claims-explorer.test.ts†L124-L145】
- EG-3: Cross-source renders are byte-identical and switching preserves state【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】

## Blockers honored
- B-1: ✅ Static mode issues no network requests【F:packages/explorer-test/claims-explorer.test.ts†L82-L87】【F:packages/explorer-test/claims-explorer.test.ts†L112-L116】
- B-2: ✅ Source switch runtime-selectable【F:docs/claims-explorer.html†L323-L346】【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】
- B-3: ✅ Default dataset/date on first load【F:docs/claims-explorer.html†L291-L313】
- B-4: ✅ Tags panel hidden with no tags【F:docs/claims-explorer.html†L180-L185】【F:packages/explorer-test/claims-explorer.test.ts†L133-L136】

## Lessons / tradeoffs (≤5 bullets)
- `/health` centralizes meta data for API and reduces redundant requests.
- Sorting tags ensures deterministic panel order across sources.
- Dedicated test package keeps jsdom scoped to tests and speeds install for other packages.

## Bench notes (optional, off-mode)
- n/a

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
