# COMPLIANCE — C1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: services/host-lite/src/server.ts
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — code link: services/host-lite/src/server.ts
- [x] ESM internal imports must include `.js` — code link: services/host-lite/src/server.ts
- [x] Tests run in parallel without cross-test state bleed — test link: services/host-lite/tests/host-lite.test.ts
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — code/test link: services/host-lite/src/server.ts
- [x] Host must not use files or external DBs; in-memory only — code link: services/host-lite/src/server.ts
- [x] Only `/plan` and `/apply` endpoints are allowed — code link: services/host-lite/src/server.ts
- [x] `/plan` and `/apply` must be idempotent — test link: services/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — test link: services/host-lite/tests/host-lite.test.ts

## Acceptance (oracle)
- [x] Enable/disable behavior (both runtimes)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (e.g., ESM)
- [x] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: services/host-lite/src/server.ts
- Tests: services/host-lite/tests/host-lite.test.ts
- CI runs: pnpm test
- Bench (off-mode, if applicable): n/a
