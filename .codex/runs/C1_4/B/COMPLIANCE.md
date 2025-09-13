# COMPLIANCE — C1 — Run 4

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas — code link: packages/host-lite/src/server.ts
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports include `.js` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Tests run in parallel without cross-test state bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Outputs deterministic via canonical bytes — code/test link: packages/host-lite/src/server.ts
- [x] Host uses in-memory state only — code link: packages/host-lite/src/server.ts
- [x] Endpoints limited to `/plan` and `/apply` — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No new runtime dependencies — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net writes) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Per-world LRU cache cap 32 — code/test link: packages/host-lite/src/server.ts

## EXTRA BLOCKERS
- [x] Do not edit `.codex/tasks/**` — n/a
- [x] No new runtime deps; Fastify removed — code link: packages/host-lite/package.json
- [x] No `as any`; ESM imports keep `.js` — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Only `/plan` and `/apply`; deterministic outputs — test link: packages/host-lite/tests/host-lite.test.ts

## Acceptance (oracle)
- [x] Enable/disable behavior (both runtimes)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (e.g., ESM)
- [x] Code quality (naming, no unnecessary clones/copies)
- [x] 404/400 canonical errors — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Multi-world cache bound proof — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Package exports main `src/server.ts` — test link: packages/host-lite/tests/host-lite.test.ts

## Evidence
- Code: packages/host-lite/src/server.ts; packages/host-lite/package.json
- Tests: packages/host-lite/tests/host-lite.test.ts
- CI runs: pnpm -F host-lite-ts test
- Bench (off-mode, if applicable): n/a
