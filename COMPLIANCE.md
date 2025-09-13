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
