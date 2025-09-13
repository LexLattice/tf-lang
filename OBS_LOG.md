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

# Observation Log — E1 — Run 1

- Strategy chosen: augment Explorer to switch data sources at runtime and apply defaults with tags-aware rendering.
- Key changes (files): docs/claims-explorer.html; packages/host-lite/test/e1.explorer-source-switch.test.ts; packages/host-lite/package.json; pnpm-lock.yaml.
- Determinism stress (runs × passes): 1× `pnpm -F host-lite-ts test` — all green.
- Near-misses vs blockers: `pnpm test` failed for services/claims-api-ts (missing vitest).
- Notes: added jsdom dev dependency for DOM-based tests.
