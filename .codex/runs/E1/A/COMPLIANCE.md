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
- [x] Prepared statements reused; no per-call prepares — code link: services/claims-api-ts/src/db.ts
- [x] Evidence samples via SQL DISTINCT/ORDER BY/LIMIT — code link: services/claims-api-ts/src/db.ts
- [x] Parameterized queries; no `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js`; no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests hermetic & deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-3)
- [x] No JS pagination/filtering on results — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Prepared statements bound/reset between runs — code link: services/claims-api-ts/src/db.ts
- [x] `.gitignore` covers SQLite binaries — code link: .gitignore
- [x] 400 on invalid shapes (limit=0, offset<0) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage proof: only sql.js imported — test link: services/claims-api-ts/test/sqlite.test.ts

## Acceptance (oracle)
- [x] Prepared vs non-prepared equivalence (stable bytes) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Evidence via SQL only — code link: services/claims-api-ts/src/db.ts
- [x] Paging determinism with large offset — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection test remains green — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`

# COMPLIANCE — D1 — Run 5

## Blockers (must all be ✅)
- [x] No kernel/schema changes — code link: services/claims-api-ts/src/app.ts
- [x] No per-call locks or `as any` — code link: services/claims-api-ts/src/db.ts
- [x] ESM internal imports include `.js` — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Tests parallel-safe, deterministic — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Storage strictly SQLite via sql.js — code link: packages/d1-sqlite/src/db.js
- [x] Responses include `dataset_version` and `query_hash` — code link: services/claims-api-ts/src/db.ts
- [x] ≥10 distinct evidence samples — test link: services/claims-api-ts/test/sqlite.test.ts

## EXTRA BLOCKERS (pass-4)
- [x] No committed DB binaries; `.gitignore` blocks artifacts — code link: .gitignore
- [x] SQL-only paging/evidence; no `.slice`/`.filter` over rows — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] All queries parameterized; hot paths prepared & reused — code link: services/claims-api-ts/src/db.ts
- [x] No `as any`; inputs validated with 400 on bad shapes — code link: services/claims-api-ts/src/filters.ts

## Acceptance (oracle)
- [x] Prepared vs ad-hoc execution byte-identical — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Injection-shaped value safe — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Paging boundaries deterministic (limit=0, large offset) — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Hygiene scan: .js imports and no deep imports — test link: services/claims-api-ts/test/sqlite.test.ts
- [x] Determinism loop across repeated runs — test link: services/claims-api-ts/test/sqlite.test.ts

## Evidence
- Code: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; packages/d1-sqlite/src/db.js; .gitignore
- Tests: services/claims-api-ts/test/sqlite.test.ts
- Runs: `pnpm --filter claims-api-ts test`; `pnpm test`
- Bench (off-mode, if applicable): n/a

# COMPLIANCE — E1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — code link: docs/claims-explorer.html
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — test link: packages/host-lite/test/e1.explorer-source-switch.test.ts
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/host-lite/test/e1.explorer-source-switch.test.ts
- [x] Static file mode does not issue network requests — code link: docs/claims-explorer.html#L211-L218
- [x] Source switching runtime-selectable — code link: docs/claims-explorer.html#L211-L229
- [x] Default dataset and date on first load — code link: docs/claims-explorer.html#L282-L289
- [x] Tags panel hidden when no tags — code link: docs/claims-explorer.html#L181-L201

## Acceptance (oracle)
- [x] Enable/disable behavior (both runtimes)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (n/a)
- [x] Build/packaging correctness (e.g., ESM)
- [x] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: docs/claims-explorer.html
- Tests: packages/host-lite/test/e1.explorer-source-switch.test.ts
- CI runs: `pnpm -F host-lite-ts test`
- Bench (off-mode, if applicable): n/a
