# Parallel run aggregation
_Winner branch: main — 2025-09-13T13:34:14Z_

---

## Run A — PR #78 (65a78ac)
_F1: docs previews and main deploy_

### REPORT.md
```md
# REPORT — F1 — Run 1

## End Goal fulfillment
- EG-1: PR builds upload a docs preview artifact while main pushes deploy to Pages【F:.github/workflows/pages.yml†L1-L32】
- EG-2: README displays a deployment badge linking to the live site【F:README.md†L3-L5】

## Blockers honored
- B-1: ✅ PR runs skip deploy; build uploads artifact only【F:.github/workflows/pages.yml†L3-L24】
- B-2: ✅ `main` branch deploys via `actions/deploy-pages@v4`【F:.github/workflows/pages.yml†L24-L32】
- B-3: ✅ README contains status badge referencing live site URL【F:README.md†L3-L5】

## Lessons / tradeoffs (≤5 bullets)
- Conditional deploy keeps preview builds private yet functional.
- Minimal badge surfaces production status without extra tooling.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E2 — Run 1

## End Goal fulfillment
- EG-1: Explorer renders provided proof tags in sorted order【F:docs/claims-explorer.html†L303-L307】【F:packages/explorer-test/claims-explorer.test.ts†L84-L107】
- EG-2: Tags panel hidden when dataset lacks tags【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】
- EG-3: Static and API renders produce identical DOM across reloads【F:packages/explorer-test/claims-explorer.test.ts†L153-L172】

## Blockers honored
- B-1: ✅ Tags rendered only from dataset data; no synthetic tags【F:docs/claims-explorer.html†L303-L307】
- B-2: ✅ Stable ordering via `localeCompare`【F:docs/claims-explorer.html†L303-L375】
- B-3: ✅ Tags panel hidden when no tags exist【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】

## Lessons / tradeoffs (≤5 bullets)
- Sorting with `localeCompare` locks stable ordering across engines.
- JSDOM timers flushed before closing to avoid stray errors.
- Tests confirm byte-identical DOM for static and API loads.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E1 — Run 2

## End Goal fulfillment
- EG-1: `/health` provides dataset version, tags and default date for API mode; static mode draws tags from dataset metadata【F:docs/claims-explorer.html†L143-L148】【F:docs/claims-explorer.html†L277-L304】
- EG-2: Default date auto-selects from `at` or `generated_at`; tags panel hidden when no tags and rendered with sorted tags when present【F:docs/claims-explorer.html†L291-L313】【F:docs/claims-explorer.html†L180-L195】【F:packages/explorer-test/claims-explorer.test.ts†L124-L145】
- EG-3: Cross-source renders are byte-identical and switching preserves state【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】

## Blockers honored
- B-1: ✅ Static mode issues no network requests【F:packages/explorer-test/claims-explorer.test.ts†L82-L87】【F:packages/explorer-test/claims-explorer.test.ts†L112-L116】
- B-2: ✅ Source switch runtime-selectable【F:docs/claims-explorer.html†L323-L346】【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】
- B-3: ✅ Default dataset/date on first load【F:docs/claims-explorer.html†L291-L313】
- B-4: ✅ Tags panel hidden with no tags【F:docs/claims-explorer.html†L180-L185】【F:packages/explorer-test/claims-explorer.test.ts†L133-L136】

## Lessons / tradeoffs (≤5 bullets)
- `/health` centralizes meta data for API and reduces redundant requests.
- Sorting tags ensures deterministic panel order across sources.
- Dedicated test package keeps jsdom scoped to tests and speeds install for other packages.

## Bench notes (optional, off-mode)
- n/a

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

# REPORT — D1 — Run 5

## End Goal fulfillment
- EG-1: SQLite adapter built in-memory from fixtures with prepared statement reuse【F:packages/d1-sqlite/src/db.js†L1-L17】【F:services/claims-api-ts/src/db.ts†L1-L78】
- EG-2: Responses return dataset_version and BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L52-L76】【F:services/claims-api-ts/test/sqlite.test.ts†L26-L36】

## Blockers honored
- B-1: ✅ No `as any`; inputs validated【F:services/claims-api-ts/src/filters.ts†L1-L32】
- B-2: ✅ ESM imports include `.js`; no deep imports【F:services/claims-api-ts/test/sqlite.test.ts†L50-L63】

## Lessons / tradeoffs (≤5 bullets)
- Guarded DB initialization yields deterministic 500s without affecting hot paths.
- Allowing limit=0 required filter adjustments but keeps paging logic in SQL.
- Prepared statements proved equivalent to ad-hoc queries, reinforcing reuse.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
- `pnpm test` — workspace tests all pass.

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

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
```

### COMPLIANCE.md
```md
# COMPLIANCE — F1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — n/a
- [x] ESM internal imports include `.js` — n/a
- [x] Tests parallel-safe, deterministic — run: `pnpm test`
- [x] PR builds artifact only, no deploy — code link: .github/workflows/pages.yml
- [x] `main` branch deploys live site — code link: .github/workflows/pages.yml
- [x] README shows deployment badge linking to live site — code link: README.md

## Acceptance (oracle)
- [x] PR workflow uploads preview artifact without deploying
- [x] Main workflow deploys to production URL
- [x] README badge points to deployed site

## Evidence
- Code: .github/workflows/pages.yml; README.md
- Runs: `pnpm test`

# COMPLIANCE — E2 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Proof tags only from dataset data — code link: docs/claims-explorer.html
- [x] Rendering order for tags stable — code link: docs/claims-explorer.html
- [x] Tags panel hidden when no tags — test link: packages/explorer-test/claims-explorer.test.ts

## Acceptance (oracle)
- [x] Dataset with proof tags shows sorted panel
- [x] Dataset without tags hides panel
- [x] Static/API renders byte-identical
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

# COMPLIANCE — E1 — Run 2

## Blockers (must all be ✅)
- [x] No kernel/schema changes — n/a
- [x] No per-call locks or `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Static mode issues no network calls — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Source switch runtime-selectable — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts
- [x] Default dataset/date on first load — code link: docs/claims-explorer.html
- [x] Tags panel hidden when dataset has no tags — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts

## EXTRA BLOCKERS (pass-2)
- [x] Tags sourced only from `/health` or static meta — code link: docs/claims-explorer.html
- [x] No network requests in static-mode tests — test link: packages/explorer-test/claims-explorer.test.ts
- [x] DOM tests isolated under `packages/explorer-test/` — code link: packages/explorer-test/package.json
- [x] Do not edit `.codex/tasks/**` — n/a

## Acceptance (oracle)
- [x] Source toggle preserves state
- [x] Offline static mode renders; API mode fails gracefully
- [x] Defaults visible on first load
- [x] Tags panel present only with tags
- [x] Deterministic output across repeats and sources
- [x] Cross-source parity snapshot
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html; packages/explorer-test/package.json
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

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
```

### OBS_LOG.md
```md
# Observation Log — F1 — Run 1

- Strategy: condition Pages workflow for PR preview artifact and main deploy; add README badge.
- Key changes: .github/workflows/pages.yml; README.md; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Notes: deploy job guarded to skip on PR.

# Observation Log — E2 — Run 1

- Strategy chosen: sort proof tags via `localeCompare` and verify static/API DOM snapshots.
- Key changes: docs/claims-explorer.html; packages/explorer-test/claims-explorer.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Near-misses vs blockers: flushed timers before closing JSDOM to avoid stray errors.
- Notes: tags rendered only from dataset data; no synthetic tags.

# Observation Log — E1 — Run 2

- Strategy: pull meta/tags from `/health`, sort tags, and isolate DOM tests in a new package.
- Key changes: docs/claims-explorer.html; packages/explorer-test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Notes: fetch stubs keep static mode offline; HTML snapshots verify cross-source parity.

# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run 3

- Strategy: parameterize SQL queries and move paging to LIMIT/OFFSET; add filter validation.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — byte-identical outputs.
- Tradeoffs: added simple manual validation to avoid extra deps; reused sql.js builder for hermetic tests.
- Notes: grep checks ensure no JS slicing or deep imports.

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: guard DB init, add limit=0 path, and compare prepared vs ad-hoc execution.
- Key changes: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: adjusted filter bounds to allow `limit=0` while keeping validation.
- Notes: rg scan expanded to entire src to enforce SQL-only pagination.
```

### CHANGES.md
```md
# F1 — Changes (Run 1)

## Summary
Pages workflow now uploads a preview artifact for pull requests and only deploys on `main`; README surfaces a status badge linking to the live site.

## Why
Allows reviewers to download a docs preview without publishing while main pushes go straight to production with visible status.

## Tests
- Determinism/parity: `pnpm test`.

## Notes
- Deploy job guarded by event check.

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
```

---

## Run B — PR #79 (20d2c36)
_F1: add Pages preview artifact and deployment badge_

### REPORT.md
```md
# REPORT — F1 — Run 1

## End Goal fulfillment
- EG-1: Pull request builds upload a preview artifact without triggering deploy【F:.github/workflows/pages.yml†L1-L27】【F:.github/workflows/pages.yml†L24-L33】
- EG-2: Pushes to `main` deploy the site to production via `deploy-pages`【F:.github/workflows/pages.yml†L24-L33】
- EG-3: README exposes a deployment badge linking to the live site【F:README.md†L3-L5】

## Blockers honored
- B-1: ✅ PR builds produce artifact only; deploy gated to `main`【F:.github/workflows/pages.yml†L1-L27】【F:.github/workflows/pages.yml†L24-L33】
- B-2: ✅ README includes deployment status badge【F:README.md†L3-L5】

## Lessons / tradeoffs (≤5 bullets)
- Conditional deploy keeps preview runs safe for forks.
- Badge offers quick status visibility in README.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E2 — Run 1

## End Goal fulfillment
- EG-1: Explorer renders provided proof tags in sorted order【F:docs/claims-explorer.html†L303-L307】【F:packages/explorer-test/claims-explorer.test.ts†L84-L107】
- EG-2: Tags panel hidden when dataset lacks tags【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】
- EG-3: Static and API renders produce identical DOM across reloads【F:packages/explorer-test/claims-explorer.test.ts†L153-L172】

## Blockers honored
- B-1: ✅ Tags rendered only from dataset data; no synthetic tags【F:docs/claims-explorer.html†L303-L307】
- B-2: ✅ Stable ordering via `localeCompare`【F:docs/claims-explorer.html†L303-L375】
- B-3: ✅ Tags panel hidden when no tags exist【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】

## Lessons / tradeoffs (≤5 bullets)
- Sorting with `localeCompare` locks stable ordering across engines.
- JSDOM timers flushed before closing to avoid stray errors.
- Tests confirm byte-identical DOM for static and API loads.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E1 — Run 2

## End Goal fulfillment
- EG-1: `/health` provides dataset version, tags and default date for API mode; static mode draws tags from dataset metadata【F:docs/claims-explorer.html†L143-L148】【F:docs/claims-explorer.html†L277-L304】
- EG-2: Default date auto-selects from `at` or `generated_at`; tags panel hidden when no tags and rendered with sorted tags when present【F:docs/claims-explorer.html†L291-L313】【F:docs/claims-explorer.html†L180-L195】【F:packages/explorer-test/claims-explorer.test.ts†L124-L145】
- EG-3: Cross-source renders are byte-identical and switching preserves state【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】

## Blockers honored
- B-1: ✅ Static mode issues no network requests【F:packages/explorer-test/claims-explorer.test.ts†L82-L87】【F:packages/explorer-test/claims-explorer.test.ts†L112-L116】
- B-2: ✅ Source switch runtime-selectable【F:docs/claims-explorer.html†L323-L346】【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】
- B-3: ✅ Default dataset/date on first load【F:docs/claims-explorer.html†L291-L313】
- B-4: ✅ Tags panel hidden with no tags【F:docs/claims-explorer.html†L180-L185】【F:packages/explorer-test/claims-explorer.test.ts†L133-L136】

## Lessons / tradeoffs (≤5 bullets)
- `/health` centralizes meta data for API and reduces redundant requests.
- Sorting tags ensures deterministic panel order across sources.
- Dedicated test package keeps jsdom scoped to tests and speeds install for other packages.

## Bench notes (optional, off-mode)
- n/a

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

# REPORT — D1 — Run 5

## End Goal fulfillment
- EG-1: SQLite adapter built in-memory from fixtures with prepared statement reuse【F:packages/d1-sqlite/src/db.js†L1-L17】【F:services/claims-api-ts/src/db.ts†L1-L78】
- EG-2: Responses return dataset_version and BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L52-L76】【F:services/claims-api-ts/test/sqlite.test.ts†L26-L36】

## Blockers honored
- B-1: ✅ No `as any`; inputs validated【F:services/claims-api-ts/src/filters.ts†L1-L32】
- B-2: ✅ ESM imports include `.js`; no deep imports【F:services/claims-api-ts/test/sqlite.test.ts†L50-L63】

## Lessons / tradeoffs (≤5 bullets)
- Guarded DB initialization yields deterministic 500s without affecting hot paths.
- Allowing limit=0 required filter adjustments but keeps paging logic in SQL.
- Prepared statements proved equivalent to ad-hoc queries, reinforcing reuse.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
- `pnpm test` — workspace tests all pass.

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

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
```

### COMPLIANCE.md
```md
# COMPLIANCE — F1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel semantics/tag schemas from A/B — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — n/a
- [x] ESM internal imports must include `.js` — n/a
- [x] Tests run in parallel without state bleed; outputs deterministic — test link: `pnpm test`
- [x] PR builds must not deploy publicly (artifacts only) — code link: .github/workflows/pages.yml
- [x] `main` branch must deploy live site — code link: .github/workflows/pages.yml
- [x] README must contain a deployment status badge referencing the live site URL — code link: README.md

## Acceptance (oracle)
- [x] PR workflow: logs show preview artifact produced; no public deploy step
- [x] Main workflow: logs confirm deploy to production URL
- [x] README badge points to deployed site

## Evidence
- Code: .github/workflows/pages.yml; README.md
- Tests: `pnpm test`
- CI runs: pages workflow

# COMPLIANCE — E2 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Proof tags only from dataset data — code link: docs/claims-explorer.html
- [x] Rendering order for tags stable — code link: docs/claims-explorer.html
- [x] Tags panel hidden when no tags — test link: packages/explorer-test/claims-explorer.test.ts

## Acceptance (oracle)
- [x] Dataset with proof tags shows sorted panel
- [x] Dataset without tags hides panel
- [x] Static/API renders byte-identical
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

# COMPLIANCE — E1 — Run 2

## Blockers (must all be ✅)
- [x] No kernel/schema changes — n/a
- [x] No per-call locks or `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Static mode issues no network calls — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Source switch runtime-selectable — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts
- [x] Default dataset/date on first load — code link: docs/claims-explorer.html
- [x] Tags panel hidden when dataset has no tags — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts

## EXTRA BLOCKERS (pass-2)
- [x] Tags sourced only from `/health` or static meta — code link: docs/claims-explorer.html
- [x] No network requests in static-mode tests — test link: packages/explorer-test/claims-explorer.test.ts
- [x] DOM tests isolated under `packages/explorer-test/` — code link: packages/explorer-test/package.json
- [x] Do not edit `.codex/tasks/**` — n/a

## Acceptance (oracle)
- [x] Source toggle preserves state
- [x] Offline static mode renders; API mode fails gracefully
- [x] Defaults visible on first load
- [x] Tags panel present only with tags
- [x] Deterministic output across repeats and sources
- [x] Cross-source parity snapshot
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html; packages/explorer-test/package.json
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

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
```

### OBS_LOG.md
```md
# Observation Log — F1 — Run 1

- Strategy: gate GitHub Pages deploy step to `main` and upload preview artifacts for PRs.
- Key changes: .github/workflows/pages.yml; README.md; CHANGES.md; COMPLIANCE.md; REPORT.md; OBS_LOG.md.
- Determinism runs: `pnpm test` — all green.
- Notes: PR runs stop before deploy; main pushes publish to live Pages site.

# Observation Log — E2 — Run 1

- Strategy chosen: sort proof tags via `localeCompare` and verify static/API DOM snapshots.
- Key changes: docs/claims-explorer.html; packages/explorer-test/claims-explorer.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Near-misses vs blockers: flushed timers before closing JSDOM to avoid stray errors.
- Notes: tags rendered only from dataset data; no synthetic tags.

# Observation Log — E1 — Run 2

- Strategy: pull meta/tags from `/health`, sort tags, and isolate DOM tests in a new package.
- Key changes: docs/claims-explorer.html; packages/explorer-test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Notes: fetch stubs keep static mode offline; HTML snapshots verify cross-source parity.

# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run 3

- Strategy: parameterize SQL queries and move paging to LIMIT/OFFSET; add filter validation.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — byte-identical outputs.
- Tradeoffs: added simple manual validation to avoid extra deps; reused sql.js builder for hermetic tests.
- Notes: grep checks ensure no JS slicing or deep imports.

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: guard DB init, add limit=0 path, and compare prepared vs ad-hoc execution.
- Key changes: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: adjusted filter bounds to allow `limit=0` while keeping validation.
- Notes: rg scan expanded to entire src to enforce SQL-only pagination.
```

### CHANGES.md
```md
# F1 — Changes (Run 1)

## Summary
GitHub Pages workflow now produces preview artifacts for pull requests and deploys to production only on `main`. README shows a deployment badge linking to the live site.

## Why
- Satisfies F1 END_GOAL: preview artifacts for PRs, live deploys on main, visible status badge.

## Tests
- Added: n/a
- Updated: n/a
- Determinism/parity: `pnpm test`

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
```

---

## Run C — PR #80 (57e9c9a)
_F1: add Pages preview and badge_

### REPORT.md
```md
# REPORT — F1 — Run 1

## End Goal fulfillment
- EG-1: PR builds upload preview artifact without public deploy【F:.github/workflows/pages.yml†L3-L12】【F:tests/pages-workflow.test.mjs†L7-L11】
- EG-2: `main` deploys site to production and README exposes badge linking to the live URL【F:.github/workflows/pages.yml†L24-L31】【F:README.md†L3-L4】

## Blockers honored
- B-1: ✅ PR builds produce artifacts only, deploy gated to `main`【F:.github/workflows/pages.yml†L24-L31】
- B-2: ✅ README badge references live site URL【F:README.md†L3-L4】

## Lessons / tradeoffs (≤5 bullets)
- Branch guard keeps preview runs private.
- Minimal workflow keeps build identical across PR and main.
- Badge leverages GitHub status for visibility.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E2 — Run 1

## End Goal fulfillment
- EG-1: Explorer renders provided proof tags in sorted order【F:docs/claims-explorer.html†L303-L307】【F:packages/explorer-test/claims-explorer.test.ts†L84-L107】
- EG-2: Tags panel hidden when dataset lacks tags【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】
- EG-3: Static and API renders produce identical DOM across reloads【F:packages/explorer-test/claims-explorer.test.ts†L153-L172】

## Blockers honored
- B-1: ✅ Tags rendered only from dataset data; no synthetic tags【F:docs/claims-explorer.html†L303-L307】
- B-2: ✅ Stable ordering via `localeCompare`【F:docs/claims-explorer.html†L303-L375】
- B-3: ✅ Tags panel hidden when no tags exist【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】

## Lessons / tradeoffs (≤5 bullets)
- Sorting with `localeCompare` locks stable ordering across engines.
- JSDOM timers flushed before closing to avoid stray errors.
- Tests confirm byte-identical DOM for static and API loads.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E1 — Run 2

## End Goal fulfillment
- EG-1: `/health` provides dataset version, tags and default date for API mode; static mode draws tags from dataset metadata【F:docs/claims-explorer.html†L143-L148】【F:docs/claims-explorer.html†L277-L304】
- EG-2: Default date auto-selects from `at` or `generated_at`; tags panel hidden when no tags and rendered with sorted tags when present【F:docs/claims-explorer.html†L291-L313】【F:docs/claims-explorer.html†L180-L195】【F:packages/explorer-test/claims-explorer.test.ts†L124-L145】
- EG-3: Cross-source renders are byte-identical and switching preserves state【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】

## Blockers honored
- B-1: ✅ Static mode issues no network requests【F:packages/explorer-test/claims-explorer.test.ts†L82-L87】【F:packages/explorer-test/claims-explorer.test.ts†L112-L116】
- B-2: ✅ Source switch runtime-selectable【F:docs/claims-explorer.html†L323-L346】【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】
- B-3: ✅ Default dataset/date on first load【F:docs/claims-explorer.html†L291-L313】
- B-4: ✅ Tags panel hidden with no tags【F:docs/claims-explorer.html†L180-L185】【F:packages/explorer-test/claims-explorer.test.ts†L133-L136】

## Lessons / tradeoffs (≤5 bullets)
- `/health` centralizes meta data for API and reduces redundant requests.
- Sorting tags ensures deterministic panel order across sources.
- Dedicated test package keeps jsdom scoped to tests and speeds install for other packages.

## Bench notes (optional, off-mode)
- n/a

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

# REPORT — D1 — Run 5

## End Goal fulfillment
- EG-1: SQLite adapter built in-memory from fixtures with prepared statement reuse【F:packages/d1-sqlite/src/db.js†L1-L17】【F:services/claims-api-ts/src/db.ts†L1-L78】
- EG-2: Responses return dataset_version and BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L52-L76】【F:services/claims-api-ts/test/sqlite.test.ts†L26-L36】

## Blockers honored
- B-1: ✅ No `as any`; inputs validated【F:services/claims-api-ts/src/filters.ts†L1-L32】
- B-2: ✅ ESM imports include `.js`; no deep imports【F:services/claims-api-ts/test/sqlite.test.ts†L50-L63】

## Lessons / tradeoffs (≤5 bullets)
- Guarded DB initialization yields deterministic 500s without affecting hot paths.
- Allowing limit=0 required filter adjustments but keeps paging logic in SQL.
- Prepared statements proved equivalent to ad-hoc queries, reinforcing reuse.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
- `pnpm test` — workspace tests all pass.

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

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
```

### COMPLIANCE.md
```md
# COMPLIANCE — F1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code link: README.md
- [x] ESM internal imports include `.js` — code link: tests/pages-workflow.test.mjs
- [x] Tests parallel-safe, deterministic — test link: tests/pages-workflow.test.mjs
- [x] PR builds produce artifacts only — code link: .github/workflows/pages.yml
- [x] `main` deploys live site — code link: .github/workflows/pages.yml
- [x] README has deployment badge to live site — code link: README.md

## Acceptance (oracle)
- [x] PR workflow uploads preview artifact; no public deploy — test link: tests/pages-workflow.test.mjs
- [x] Main workflow deploys to production URL — code link: .github/workflows/pages.yml
- [x] README badge points to deployed site — code link: README.md

## Evidence
- Code: .github/workflows/pages.yml; README.md; package.json; tests/pages-workflow.test.mjs
- Tests: tests/pages-workflow.test.mjs
- Runs: `pnpm test`

# COMPLIANCE — E2 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Proof tags only from dataset data — code link: docs/claims-explorer.html
- [x] Rendering order for tags stable — code link: docs/claims-explorer.html
- [x] Tags panel hidden when no tags — test link: packages/explorer-test/claims-explorer.test.ts

## Acceptance (oracle)
- [x] Dataset with proof tags shows sorted panel
- [x] Dataset without tags hides panel
- [x] Static/API renders byte-identical
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

# COMPLIANCE — E1 — Run 2

## Blockers (must all be ✅)
- [x] No kernel/schema changes — n/a
- [x] No per-call locks or `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Static mode issues no network calls — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Source switch runtime-selectable — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts
- [x] Default dataset/date on first load — code link: docs/claims-explorer.html
- [x] Tags panel hidden when dataset has no tags — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts

## EXTRA BLOCKERS (pass-2)
- [x] Tags sourced only from `/health` or static meta — code link: docs/claims-explorer.html
- [x] No network requests in static-mode tests — test link: packages/explorer-test/claims-explorer.test.ts
- [x] DOM tests isolated under `packages/explorer-test/` — code link: packages/explorer-test/package.json
- [x] Do not edit `.codex/tasks/**` — n/a

## Acceptance (oracle)
- [x] Source toggle preserves state
- [x] Offline static mode renders; API mode fails gracefully
- [x] Defaults visible on first load
- [x] Tags panel present only with tags
- [x] Deterministic output across repeats and sources
- [x] Cross-source parity snapshot
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html; packages/explorer-test/package.json
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

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
```

### OBS_LOG.md
```md
# Observation Log — F1 — Run 1

- Strategy chosen: extend Pages workflow for PR previews and gate deploys to `main`; expose live badge in README.
- Key changes (files): .github/workflows/pages.yml; README.md; tests/pages-workflow.test.mjs; package.json; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress (runs × passes): `pnpm test` — all green.
- Near-misses vs blockers: ensured deploy step skipped on PRs via `if` guard.
- Notes: preview artifact uses `upload-pages-artifact`; badge links to live site.

# Observation Log — E2 — Run 1

- Strategy chosen: sort proof tags via `localeCompare` and verify static/API DOM snapshots.
- Key changes: docs/claims-explorer.html; packages/explorer-test/claims-explorer.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Near-misses vs blockers: flushed timers before closing JSDOM to avoid stray errors.
- Notes: tags rendered only from dataset data; no synthetic tags.

# Observation Log — E1 — Run 2

- Strategy: pull meta/tags from `/health`, sort tags, and isolate DOM tests in a new package.
- Key changes: docs/claims-explorer.html; packages/explorer-test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Notes: fetch stubs keep static mode offline; HTML snapshots verify cross-source parity.

# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run 3

- Strategy: parameterize SQL queries and move paging to LIMIT/OFFSET; add filter validation.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — byte-identical outputs.
- Tradeoffs: added simple manual validation to avoid extra deps; reused sql.js builder for hermetic tests.
- Notes: grep checks ensure no JS slicing or deep imports.

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: guard DB init, add limit=0 path, and compare prepared vs ad-hoc execution.
- Key changes: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: adjusted filter bounds to allow `limit=0` while keeping validation.
- Notes: rg scan expanded to entire src to enforce SQL-only pagination.
```

### CHANGES.md
```md
# F1 — Changes (Run 1)

## Summary
GitHub Pages workflow builds docs for pull requests as downloadable preview artifacts and deploys on `main`. The README now exposes a deployment badge linking to the live site.

## Why
- PR runs provide artifacts without public deploys per END_GOAL.
- Pushes to `main` keep the site live.

## Tests
- Added: tests/pages-workflow.test.mjs.
- Updated: .github/workflows/pages.yml; README.md; package.json.
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
```

---

## Run D — PR #81 (ac72122)
_F1: add pages preview workflow and deployment badge_

### REPORT.md
```md
# REPORT — F1 — Run 1

## End Goal fulfillment
- EG-1: PR builds upload preview artifacts without deploying【F:.github/workflows/pages.yml†L1-L26】
- EG-2: `main` deploys site to production URL【F:.github/workflows/pages.yml†L24-L33】
- EG-3: README exposes live deployment badge linking to site【F:README.md†L4-L6】

## Blockers honored
- B-1: ✅ PR builds do not deploy publicly【F:.github/workflows/pages.yml†L24-L26】
- B-2: ✅ `main` branch deploys live site【F:.github/workflows/pages.yml†L24-L33】
- B-3: ✅ README badge references live site URL【F:README.md†L4-L6】

## Lessons / tradeoffs (≤5 bullets)
- Conditional deploy keeps PR runs safe while reusing the same build job.
- Hardcoded owner in badge; assumes repository remains under `LexLattice`.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E2 — Run 1

## End Goal fulfillment
- EG-1: Explorer renders provided proof tags in sorted order【F:docs/claims-explorer.html†L303-L307】【F:packages/explorer-test/claims-explorer.test.ts†L84-L107】
- EG-2: Tags panel hidden when dataset lacks tags【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】
- EG-3: Static and API renders produce identical DOM across reloads【F:packages/explorer-test/claims-explorer.test.ts†L153-L172】

## Blockers honored
- B-1: ✅ Tags rendered only from dataset data; no synthetic tags【F:docs/claims-explorer.html†L303-L307】
- B-2: ✅ Stable ordering via `localeCompare`【F:docs/claims-explorer.html†L303-L375】
- B-3: ✅ Tags panel hidden when no tags exist【F:packages/explorer-test/claims-explorer.test.ts†L139-L150】

## Lessons / tradeoffs (≤5 bullets)
- Sorting with `localeCompare` locks stable ordering across engines.
- JSDOM timers flushed before closing to avoid stray errors.
- Tests confirm byte-identical DOM for static and API loads.

## Bench notes (optional, off-mode)
- n/a

## Self-review
- [x] `pnpm test` passes
- [x] All blockers satisfied
- [x] No extraneous commits or files
- [x] No `as any`, per-call locks, or schema changes

# REPORT — E1 — Run 2

## End Goal fulfillment
- EG-1: `/health` provides dataset version, tags and default date for API mode; static mode draws tags from dataset metadata【F:docs/claims-explorer.html†L143-L148】【F:docs/claims-explorer.html†L277-L304】
- EG-2: Default date auto-selects from `at` or `generated_at`; tags panel hidden when no tags and rendered with sorted tags when present【F:docs/claims-explorer.html†L291-L313】【F:docs/claims-explorer.html†L180-L195】【F:packages/explorer-test/claims-explorer.test.ts†L124-L145】
- EG-3: Cross-source renders are byte-identical and switching preserves state【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】

## Blockers honored
- B-1: ✅ Static mode issues no network requests【F:packages/explorer-test/claims-explorer.test.ts†L82-L87】【F:packages/explorer-test/claims-explorer.test.ts†L112-L116】
- B-2: ✅ Source switch runtime-selectable【F:docs/claims-explorer.html†L323-L346】【F:packages/explorer-test/claims-explorer.test.ts†L82-L109】
- B-3: ✅ Default dataset/date on first load【F:docs/claims-explorer.html†L291-L313】
- B-4: ✅ Tags panel hidden with no tags【F:docs/claims-explorer.html†L180-L185】【F:packages/explorer-test/claims-explorer.test.ts†L133-L136】

## Lessons / tradeoffs (≤5 bullets)
- `/health` centralizes meta data for API and reduces redundant requests.
- Sorting tags ensures deterministic panel order across sources.
- Dedicated test package keeps jsdom scoped to tests and speeds install for other packages.

## Bench notes (optional, off-mode)
- n/a

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

# REPORT — D1 — Run 5

## End Goal fulfillment
- EG-1: SQLite adapter built in-memory from fixtures with prepared statement reuse【F:packages/d1-sqlite/src/db.js†L1-L17】【F:services/claims-api-ts/src/db.ts†L1-L78】
- EG-2: Responses return dataset_version and BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L52-L76】【F:services/claims-api-ts/test/sqlite.test.ts†L26-L36】

## Blockers honored
- B-1: ✅ No `as any`; inputs validated【F:services/claims-api-ts/src/filters.ts†L1-L32】
- B-2: ✅ ESM imports include `.js`; no deep imports【F:services/claims-api-ts/test/sqlite.test.ts†L50-L63】

## Lessons / tradeoffs (≤5 bullets)
- Guarded DB initialization yields deterministic 500s without affecting hot paths.
- Allowing limit=0 required filter adjustments but keeps paging logic in SQL.
- Prepared statements proved equivalent to ad-hoc queries, reinforcing reuse.

## Determinism runs
- `pnpm --filter claims-api-ts test` repeated 3× — stable.
- `pnpm test` — workspace tests all pass.

# REPORT — D1 — Run 4

## End Goal fulfillment
- G1: Reused prepared statements serve counts, lists, and evidence directly from SQL【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/src/db.ts†L58-L74】
- G2: Responses include dataset version and canonical BLAKE3 query_hash with ≥10 distinct evidence samples【F:services/claims-api-ts/src/db.ts†L58-L74】【F:services/claims-api-ts/test/sqlite.test.ts†L24-L44】
- G3: Boundary filters (limit=0, offset<0, large offset) validated with deterministic bytes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L46-L64】

## Blockers honored
- B-1: No JS slicing/filtering; prepared statements reset for reuse【F:services/claims-api-ts/src/db.ts†L22-L44】【F:services/claims-api-ts/test/sqlite.test.ts†L33-L44】
- B-2: Only sql.js imported; SQLite binaries ignored via .gitignore【F:services/claims-api-ts/test/sqlite.test.ts†L12-L21】【F:.gitignore†L62-L65】
- B-3: 400 responses for invalid filter shapes【F:services/claims-api-ts/src/filters.ts†L18-L30】【F:services/claims-api-ts/test/sqlite.test.ts†L66-L74】

## Lessons / tradeoffs (≤5 bullets)
- Prepared statement caching reduces compile overhead but assumes single-process reuse.
- SQL DISTINCT/ORDER BY ensures evidence uniqueness without JS post-processing.
- Large-offset queries still run count statements; no early abort implemented.

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
```

### COMPLIANCE.md
```md
# COMPLIANCE — F1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel semantics/tag schemas — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — n/a
- [x] ESM internal imports include `.js` — n/a
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/pages-workflow.test.ts
- [x] PR builds must not deploy publicly — workflow link: .github/workflows/pages.yml
- [x] main branch must deploy live site — workflow link: .github/workflows/pages.yml
- [x] README must contain a deployment status badge referencing the live site URL — code link: README.md

## Acceptance (oracle)
- [x] PR workflow: preview artifact produced; no deploy — workflow link: .github/workflows/pages.yml
- [x] Main workflow: deploys to production URL — workflow link: .github/workflows/pages.yml
- [x] README badge points to deployed site — code link: README.md
- [x] Build/packaging correctness (ESM) — n/a
- [x] Code quality (minimal diff)

## Evidence
- Code: .github/workflows/pages.yml; README.md
- Tests: packages/explorer-test/pages-workflow.test.ts
- Runs: `pnpm test`

# COMPLIANCE — E2 — Run 1

## Blockers (must all be ✅)
- [x] No changes to kernel/tag schemas — n/a
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Proof tags only from dataset data — code link: docs/claims-explorer.html
- [x] Rendering order for tags stable — code link: docs/claims-explorer.html
- [x] Tags panel hidden when no tags — test link: packages/explorer-test/claims-explorer.test.ts

## Acceptance (oracle)
- [x] Dataset with proof tags shows sorted panel
- [x] Dataset without tags hides panel
- [x] Static/API renders byte-identical
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

# COMPLIANCE — E1 — Run 2

## Blockers (must all be ✅)
- [x] No kernel/schema changes — n/a
- [x] No per-call locks or `as any` — code link: docs/claims-explorer.html
- [x] ESM internal imports include `.js` — code link: docs/claims-explorer.html
- [x] Tests parallel-safe, deterministic — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Static mode issues no network calls — test link: packages/explorer-test/claims-explorer.test.ts
- [x] Source switch runtime-selectable — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts
- [x] Default dataset/date on first load — code link: docs/claims-explorer.html
- [x] Tags panel hidden when dataset has no tags — code/test link: docs/claims-explorer.html / packages/explorer-test/claims-explorer.test.ts

## EXTRA BLOCKERS (pass-2)
- [x] Tags sourced only from `/health` or static meta — code link: docs/claims-explorer.html
- [x] No network requests in static-mode tests — test link: packages/explorer-test/claims-explorer.test.ts
- [x] DOM tests isolated under `packages/explorer-test/` — code link: packages/explorer-test/package.json
- [x] Do not edit `.codex/tasks/**` — n/a

## Acceptance (oracle)
- [x] Source toggle preserves state
- [x] Offline static mode renders; API mode fails gracefully
- [x] Defaults visible on first load
- [x] Tags panel present only with tags
- [x] Deterministic output across repeats and sources
- [x] Cross-source parity snapshot
- [x] Build/packaging correctness (ESM)
- [x] Code quality

## Evidence
- Code: docs/claims-explorer.html; packages/explorer-test/package.json
- Tests: packages/explorer-test/claims-explorer.test.ts
- Runs: `pnpm test`

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
```

### OBS_LOG.md
```md
# Observation Log — F1 — Run 1

- Strategy chosen: add PR preview artifact build and main deployment; surface live badge in README.
- Key changes (files): .github/workflows/pages.yml; README.md; packages/explorer-test/pages-workflow.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress (runs × passes): `pnpm test` ×1 — stable.
- Near-misses vs blockers: none.
- Notes: badge links to GitHub Pages; deploy job gated on `main`.

# Observation Log — E2 — Run 1

- Strategy chosen: sort proof tags via `localeCompare` and verify static/API DOM snapshots.
- Key changes: docs/claims-explorer.html; packages/explorer-test/claims-explorer.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Near-misses vs blockers: flushed timers before closing JSDOM to avoid stray errors.
- Notes: tags rendered only from dataset data; no synthetic tags.

# Observation Log — E1 — Run 2

- Strategy: pull meta/tags from `/health`, sort tags, and isolate DOM tests in a new package.
- Key changes: docs/claims-explorer.html; packages/explorer-test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: `pnpm test` — all green.
- Notes: fetch stubs keep static mode offline; HTML snapshots verify cross-source parity.

# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).

# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON loader with CLI-backed SQLite adapter; add BLAKE3 hashing.
- Key changes (files): services/claims-api-ts/src/db.ts; services/claims-api-ts/src/util.ts; services/claims-api-ts/src/server.ts; services/claims-api-ts/test/sqlite.test.ts; services/claims-api-ts/data/claims.db.
- Determinism stress (runs × passes): 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: initial attempt with `sql.js` dropped due to build complexity; switched to `sqlite3` CLI.
- Notes: evidence generation uses first 10 ordered rows; CLI keeps storage SQLite-only.

# Observation Log — D1 — Run 2

- Strategy: drop file-backed SQLite and rebuild dataset via sql.js using schema/seed fixtures.
- Key changes: packages/d1-sqlite/src/db.js; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/server.ts; tests updated for determinism and storage proof.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: sql.js wasm load adds slight startup cost but avoids native deps; fixtures read once at init.
- Notes: added .gitignore entries to prevent accidental commit of DB artifacts.

# Observation Log — D1 — Run 3

- Strategy: parameterize SQL queries and move paging to LIMIT/OFFSET; add filter validation.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/src/app.ts; services/claims-api-ts/src/filters.ts; test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — byte-identical outputs.
- Tradeoffs: added simple manual validation to avoid extra deps; reused sql.js builder for hermetic tests.
- Notes: grep checks ensure no JS slicing or deep imports.

# Observation Log — D1 — Run 4

- Strategy: reuse prepared statements and keep evidence sampling purely in SQL; extend filter tests for boundary cases.
- Key changes: services/claims-api-ts/src/db.ts; services/claims-api-ts/test/sqlite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable, byte-identical.
- Tradeoffs: cached statements reset per call; simple grep guard for `.slice`/`.filter` may miss dynamic cases but keeps surface small.
- Notes: large-offset queries exercised to prove SQL paging with no JS post-processing.

# Observation Log — D1 — Run 5

- Strategy: guard DB init, add limit=0 path, and compare prepared vs ad-hoc execution.
- Key changes: services/claims-api-ts/src/app.ts; services/claims-api-ts/src/db.ts; services/claims-api-ts/src/filters.ts; services/claims-api-ts/test/sqlite.test.ts.
- Determinism stress: 3× `pnpm --filter claims-api-ts test` — stable.
- Near-misses vs blockers: adjusted filter bounds to allow `limit=0` while keeping validation.
- Notes: rg scan expanded to entire src to enforce SQL-only pagination.
```

### CHANGES.md
```md
# F1 — Changes (Run 1)

## Summary
Configure Pages workflow to publish preview artifacts on pull requests and deploy the site from `main`; add a README badge linking to the live site.

## Why
Ensures safe preview builds for contributors while keeping `main` deployments automatic and visible.

## Tests
- Added: packages/explorer-test/pages-workflow.test.ts.
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
```
