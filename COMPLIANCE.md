# COMPLIANCE — D1 — Run 1

## Blockers (must all be ✅)
- [ ] No kernel/tag schema changes — code link: n/a
- [ ] No unsafe locks/`as any` — code link: n/a
- [ ] ESM internal imports include `.js` — code link: `services/claims-api-ts/src/server.ts`
- [ ] SQLite only for storage — code link: `packages/adapter-legal-ts/src/sqlite.ts`
- [ ] Responses carry `dataset_version` and BLAKE3 `query_hash` — code link: `services/claims-api-ts/src/server.ts`
- [ ] Stable counts/clauses; ≥10 samples — test link: `services/claims-api-ts/test/sqlite.test.ts`

## Acceptance (oracle)
- [ ] Enable/disable behavior (both runtimes)
- [ ] Cache: cold→warm; reset forces re-read; no per-call locks
- [ ] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [ ] Build/packaging correctness (e.g., ESM)
- [ ] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: see linked files above
- Tests: `pnpm test`
- CI runs: n/a
- Bench (off-mode, if applicable): n/a
