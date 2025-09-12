# COMPLIANCE — C1 — Run 001

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — no kernel files touched.
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — see `packages/host-lite/src/index.ts`.
- [x] ESM internal imports must include `.js` — see `packages/host-lite/src/index.ts`.
- [x] Tests run in parallel without cross-test state bleed — `packages/host-lite/tests/host-lite.test.ts`.
- [x] Outputs must be deterministic (canonical JSON bytes & hashes) — `packages/host-lite/src/index.ts`.
- [x] Host must not use files or external DBs; in-memory only — `packages/host-lite/src/index.ts`.
- [x] Only `/plan` and `/apply` endpoints are allowed — `packages/host-lite/src/index.ts`.
- [x] `/plan` and `/apply` must be idempotent — `packages/host-lite/tests/host-lite.test.ts`.
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — `packages/host-lite/src/index.ts` and tests.

## Acceptance (oracle)
- [x] Enable/disable behavior — proof field toggled by `DEV_PROOFS`.
- [x] Cache: cold→warm; reset forces re-read; no per-call locks — request caches in host.
- [x] Parallel determinism (repeat runs stable) — tests show repeatable bytes.
- [x] Cross-runtime parity (if applicable) — n/a.
- [x] Build/packaging correctness (e.g., ESM) — package uses ESM imports with `.js`.
- [x] Code quality (naming, no unnecessary clones/copies) — reviewed.

## Evidence
- Code: `packages/host-lite/src/index.ts`
- Tests: `packages/host-lite/tests/host-lite.test.ts`
- CI runs: pending
- Bench (off-mode, if applicable): n/a
