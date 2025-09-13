# COMPLIANCE — C1 — Run 2

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas — code: `packages/host-lite/src/index.ts`
- [x] No per-call locks; no `static mut`/`unsafe`; no TS `as any` — code: `packages/host-lite/src/index.ts`
- [x] ESM internal imports include `.js` — code: `packages/host-lite/tests/host-lite.test.ts`
- [x] Tests run in parallel without cross-test state bleed — test: `packages/host-lite/tests/host-lite.test.ts`
- [x] Outputs deterministic (canonical JSON & hashes) — code/test: `packages/host-lite/src/index.ts`, `packages/host-lite/tests/host-lite.test.ts`
- [x] Host uses in-memory state only; no external persistence — code: `packages/host-lite/src/index.ts`
- [x] Only `/plan` and `/apply` endpoints exposed — code: `packages/host-lite/src/index.ts`
- [x] `/plan` and `/apply` are idempotent — test: `packages/host-lite/tests/host-lite.test.ts`
- [x] Proof artifacts gated behind `DEV_PROOFS=1` — test: `packages/host-lite/tests/host-lite.test.ts`

## EXTRA BLOCKERS
- [x] No new runtime dependencies; removed Fastify.
- [x] Tests hermetic (no sockets/files/network) — test: `packages/host-lite/tests/host-lite.test.ts`
- [x] No `as any` casts; ESM imports keep `.js` — code/test links above.
- [x] Endpoint surface fixed; outputs deterministic — code: `packages/host-lite/src/index.ts`
- [x] No deep cross-package imports; only public exports — code: `packages/host-lite/src/index.ts`

## Acceptance (oracle)
- [x] Idempotent plan/apply responses — `packages/host-lite/tests/host-lite.test.ts`
- [x] Canonical journals and proof gating — `packages/host-lite/tests/host-lite.test.ts`
- [x] Isolation: host is in-memory and ephemeral — `packages/host-lite/tests/host-lite.test.ts`
- [x] 404 for non-endpoints — `packages/host-lite/tests/host-lite.test.ts`

## Evidence
- Code: `packages/host-lite/src/index.ts`; `packages/tf-lang-l0-ts/src/index.ts`
- Tests: `packages/host-lite/tests/host-lite.test.ts`
- CI runs: `pnpm build`, `pnpm test`
