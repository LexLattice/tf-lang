# REPORT — D1 — Run 1

## End Goal fulfillment
- EG-1: SQLite adapter added; counts and clauses now sourced from SQLite with dataset version and canonical BLAKE3 hashes — see services/claims-api-ts/src/db.ts and util.ts.
- EG-2: Responses return ≥10 stable evidence samples; duplicate queries yield identical counts — verified in services/claims-api-ts/test/sqlite.test.ts.

## Blockers honored
- B-1: ✅ Storage strictly SQLite, no other DBs — services/claims-api-ts/src/db.ts.
- B-2: ✅ Deterministic hashing and responses, no per-call locks or `as any` — services/claims-api-ts/src/util.ts, test/sqlite.test.ts.

## Lessons / tradeoffs (≤5 bullets)
- Switched from native binding to wasm `sql.js` to avoid build-time native dependency.
- Duplicated sample data in tests to meet evidence-count requirement without altering real dataset.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
