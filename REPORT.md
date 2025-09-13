# REPORT — D1 — Run 1

## End Goal fulfillment
- EG-1: Claims API queries via SQLite adapter for counts/clauses【F:services/claims-api-ts/src/server.ts:1-4】【F:packages/adapter-legal-ts/src/sqlite.ts:55-62】
- EG-2: Responses include `dataset_version` and canonical BLAKE3 `query_hash`【F:services/claims-api-ts/src/server.ts:24-37】【F:services/claims-api-ts/src/util.ts:2-12】

## Blockers honored
- B-1: ✅ Storage strictly SQLite (`sqlite3` CLI)【F:packages/adapter-legal-ts/src/sqlite.ts:15-23】
- B-2: ✅ ≥10 evidence samples, deterministic counts【F:packages/adapter-legal-ts/src/sqlite.ts:55-57】【F:services/claims-api-ts/test/sqlite.test.ts:33-47】

## Lessons / tradeoffs (≤5 bullets)
- Native bindings were avoided in favor of the `sqlite3` CLI for portability.
- Query hashing with `@noble/hashes` keeps responses stable across runs.
- Sample count fixed at 10 to meet evidence requirement.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
