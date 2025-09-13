# F1 — Changes (Run 1)

## Summary
Configure Pages workflow to publish preview artifacts on pull requests and deploy the site from `main`; add a README badge linking to the live site.

## Why
Ensures safe preview builds for contributors while keeping `main` deployments automatic and visible.

## Tests
- Added: packages/explorer-test/pages-workflow.test.ts.
- Updated: packages/explorer-test/pages-workflow.test.ts (harden regex).
- Determinism/parity: `pnpm test`.

## Notes
- No schema changes; minimal surface.

# E2 — Changes (Run 1)

## Summary
Proof tags are sorted deterministically and hidden when absent to keep Explorer UI stable across static and API sources.

## Why
- Ensures stable tag ordering and conditional panel per END_GOAL.

## Tests
- Added: packages/explorer-test/claims-explorer.test.ts.
- Updated: docs/claims-explorer.html; packages/explorer-test/claims-explorer.test.ts.
- Determinism/parity: `pnpm test`.

## Notes
- No schema changes; minimal surface.

# E1 — Changes (Run 2)

## Summary
Explorer reads dataset version, tags and default date from `/health` in API mode, derives static tags from dataset metadata, and relocates DOM tests into a dedicated `packages/explorer-test` package.

## Why
- `/health` provides a single deterministic source for meta and tags.
- Packaging isolates jsdom to test-only code and keeps static mode offline.

## Tests
- Added: `packages/explorer-test/claims-explorer.test.ts`.
- Updated: `docs/claims-explorer.html`.
- Determinism/parity: repeated `pnpm test` stable.

## Notes
- No schema changes; minimal surface.

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

# F2 — Changes (Run 2)

See PR body.
