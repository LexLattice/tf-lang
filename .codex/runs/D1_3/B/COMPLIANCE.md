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
- [x] In-memory sql.js builder with fixtures — code link: packages/d1-sqlite/src/db.js
- [x] Prepared, parameterized SQL with ORDER BY and LIMIT/OFFSET — code link: services/claims-api-ts/src/db.ts
- [x] Canonical BLAKE3 `query_hash` and dataset version — code link: services/claims-api-ts/src/db.ts
- [x] Input validation; 400 on invalid shapes — code link: services/claims-api-ts/src/filters.ts; test link: services/claims-api-ts/test/sqlite.test.ts
- [x] No `as any`; typed DTOs — code link: services/claims-api-ts/src/types.ts
- [x] Injection-shaped value treated as plain string — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples via SQL DISTINCT/ORDER BY/LIMIT — code/test link: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts
- [x] ESM internal imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & parallel-safe — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] .gitignore blocks `.db`/`.sqlite*` — code link: .gitignore

## EXTRA BLOCKERS (pass-3)
- Prepared statements reused; all queries parameterized — code link: services/claims-api-ts/src/db.ts
- Evidence via SQL only; no `.slice`/`.filter` on results — test link: services/claims-api-ts/test/sqlite.test.ts
- Boundary validation (`limit=0`, negative `offset`) → 400 — test link: services/claims-api-ts/test/sqlite.test.ts
- No sqlite binaries tracked; only `sql.js` imported — code link: .gitignore; test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs non-prepared queries yield byte-identical JSON — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Evidence sampling purely via SQL; static scan for `.slice`/`.filter` — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Paging determinism: limit/offset stable over 3 runs — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection value `' OR 1=1 --` remains harmless — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; packages/d1-sqlite/src/db.js; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`; `pnpm test`
