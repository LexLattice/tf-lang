# REPORT — D1 — Run 1

## End Goal fulfillment
- EG-1: Claims API uses a SQLite adapter for counts/clauses (`sql.js` database queries) — see `services/claims-api-ts/src/server.ts`.
- EG-2: Each response includes `dataset_version`, canonical BLAKE3 `query_hash`, and ≥10 evidence samples — see `services/claims-api-ts/src/server.ts` and `services/claims-api-ts/test/d1.sqlite-adapter.test.ts`.

## Blockers honored
- B-1: ✅ No kernel/tag schema changes — no kernel files modified.
- B-2: ✅ No `as any`; imports use `.js`; storage strictly SQLite — verified in code/test.

## Lessons / tradeoffs
- Switched from native drivers to `sql.js` to avoid build-script blockers.
- BLAKE3 implemented via `@noble/hashes` for portability.
- Minimal API surface change: server factory exported for tests.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
