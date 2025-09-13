# COMPLIANCE — D1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel semantics/tag schemas from A/B — no kernel files touched.
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — all code typed; search confirms none.
- [x] ESM internal imports include `.js` — server/test imports use explicit `.js` extensions.
- [x] Tests run in parallel without state bleed; outputs deterministic (canonical bytes + BLAKE3) — `d1.sqlite-adapter.test.ts` uses isolated temp DB and checks deterministic hash.
- [x] Storage is strictly SQLite (no other DBs/networked storage) — `sql.js` loads SQLite file for all queries.
- [x] Responses include `dataset_version` and canonical BLAKE3 `query_hash` — implemented in `util.ts` and served in `server.ts`.
- [x] Identical queries do not vary in counts/clauses; ≥10 evidence samples returned — test verifies stable count and ≥10 samples.

## Acceptance (oracle)
- [x] Storage: runtime/tests confirm all IO is via SQLite only.
- [x] Hashes/versions: `dataset_version` and canonical BLAKE3 `query_hash` match expected values.
- [x] Stability: two identical queries return identical counts/clauses.
- [x] Evidence: at least ten sample evidences are included per response.

## Evidence
- Code: `services/claims-api-ts/src/server.ts`, `services/claims-api-ts/src/util.ts`.
- Tests: `services/claims-api-ts/test/d1.sqlite-adapter.test.ts`.
- CI runs: `pnpm test`.
- Bench (off-mode, if applicable): n/a.
