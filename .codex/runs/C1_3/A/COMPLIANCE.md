# COMPLIANCE — C1 — Run 3

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: packages/host-lite/src/server.ts
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — code link: packages/host-lite/src/server.ts
- [x] ESM internal imports must include `.js` — code link: packages/host-lite/src/server.ts
- [x] Tests run in parallel without cross-test state bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — code/test link: packages/host-lite/src/server.ts
- [x] Host must not use files or external DBs; in-memory only — code link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply` endpoints are allowed — code link: packages/host-lite/src/server.ts
- [x] `/plan` and `/apply` must be idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS
- [x] Do not edit `.codex/tasks/**` — confirmed
- [x] No new runtime deps — code link: packages/host-lite/package.json
- [x] Tests hermetic (no sockets/files/net) — test link: packages/host-lite/tests/host-lite.test.ts
- [x] No `as any`; ESM imports include `.js`; no per-call locks; no cross-test bleed — code/test link: packages/host-lite/src/server.ts
- [x] Only `/plan` and `/apply`; outputs deterministic — test link: packages/host-lite/tests/host-lite.test.ts

## Acceptance (oracle)
- [x] Enable/disable behavior (both runtimes)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (e.g., ESM)
- [x] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: packages/host-lite/src/server.ts
- Tests: packages/host-lite/tests/host-lite.test.ts
- CI runs: pnpm test
- Bench (off-mode, if applicable): n/a
