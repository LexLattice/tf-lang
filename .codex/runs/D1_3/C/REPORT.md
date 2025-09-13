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

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Prepared statements cached and reused for counts, evidence, and lists【F:services/claims-api-ts/src/db.ts†L41-L74】【F:services/claims-api-ts/src/db.ts†L83-L98】
- G2: Evidence sampling via SQL DISTINCT/ORDER BY/LIMIT yields ≥10 unique samples【F:services/claims-api-ts/src/db.ts†L68-L73】【F:services/claims-api-ts/test/sqlite.test.ts†L31-L40】
- G3: Strict filter parsing rejects bad paging shapes with 400 responses【F:services/claims-api-ts/src/filters.ts†L21-L29】【F:services/claims-api-ts/test/sqlite.test.ts†L85-L93】

## Blockers honored
- B-1: No JS pagination or filtering; LIMIT/OFFSET handled in SQL【F:services/claims-api-ts/src/db.ts†L83-L98】【F:services/claims-api-ts/test/sqlite.test.ts†L59-L82】
- B-2: Only sql.js imported; no native sqlite bindings【F:services/claims-api-ts/test/sqlite.test.ts†L18-L26】
- B-3: Injection-shaped value treated as data, not SQL【F:services/claims-api-ts/test/sqlite.test.ts†L110-L116】

## Lessons / tradeoffs (≤5 bullets)
- Map-based statement cache keeps implementation simple while enabling reuse.
- SQL-only evidence and paging avoid JS-level slicing/filtering.
- Boundary checks ensure invalid limit/offsets return 400 consistently.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
