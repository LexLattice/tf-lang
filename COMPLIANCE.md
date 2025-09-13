# COMPLIANCE — D1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel semantics/tag schemas from A/B — code link: (no kernel files touched).
- [x] No per-call locks; no static mut/unsafe; no TS `as any` — code link: services/claims-api-ts/src.
- [x] ESM internal imports include `.js` — code link: services/claims-api-ts/src/server.ts.
- [x] Tests run in parallel without state bleed; outputs deterministic — test link: services/claims-api-ts/test/sqlite.test.ts.
- [x] Storage strictly SQLite — code link: services/claims-api-ts/src/db.ts.
- [x] Responses include `dataset_version` and canonical BLAKE3 `query_hash` — code link: services/claims-api-ts/src/util.ts, server.ts.
- [x] Identical queries stable with ≥10 evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts.

## Acceptance (oracle)
- [x] Storage: runtime/tests confirm all IO is via SQLite only.
- [x] Hashes/versions: `dataset_version` and canonical BLAKE3 `query_hash` match expected values.
- [x] Stability: two identical queries return identical counts/clauses.
- [x] Evidence: at least ten sample evidences are included per response.

## Evidence
- Code: services/claims-api-ts/src/db.ts, util.ts, server.ts; packages/claims-core-ts/src/query.ts.
- Tests: services/claims-api-ts/test/sqlite.test.ts.
- CI runs: (see PR checks).
- Bench (off-mode, if applicable): n/a.
