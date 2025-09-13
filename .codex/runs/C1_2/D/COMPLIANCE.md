# COMPLIANCE — C1 — Run 2

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: packages/host-lite/src/index.ts
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — code link: packages/host-lite/src/index.ts
- [x] ESM internal imports must include `.js` — code/test link: packages/host-lite/src/index.ts; packages/host-lite/tests/host-lite.test.ts
- [x] Tests run in parallel without cross-test state bleed — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — code/test link: packages/host-lite/src/index.ts; packages/host-lite/tests/host-lite.test.ts
- [x] Host must not use files or external DBs; in-memory only — code link: packages/host-lite/src/index.ts
- [x] Only `/plan` and `/apply` endpoints are allowed — code link: packages/host-lite/src/index.ts
- [x] `/plan` and `/apply` must be idempotent — test link: packages/host-lite/tests/host-lite.test.ts
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — test link: packages/host-lite/tests/host-lite.test.ts

## EXTRA BLOCKERS
- [x] No new runtime deps unless necessary — `packages/host-lite/package.json`
- [x] Tests are hermetic: no open sockets or network calls — `packages/host-lite/tests/host-lite.test.ts`
- [x] Explicit 404 for non-endpoints — `packages/host-lite/src/index.ts`
- [x] No deep relative imports across packages — `packages/host-lite/tests/host-lite.test.ts`

## Acceptance (oracle)
- [x] Enable/disable behavior (proof gating)
- [x] Cache: cold→warm; reset forces re-read; no per-call locks
- [x] Parallel determinism (repeat runs stable)
- [ ] Cross-runtime parity (if applicable)
- [x] Build/packaging correctness (ESM, public exports)
- [x] Code quality (naming, no unnecessary clones/copies)

## Evidence
- Code: packages/host-lite/src/index.ts; packages/tf-lang-l0-ts/src/index.ts
- Tests: packages/host-lite/tests/host-lite.test.ts
- CI runs: `pnpm -F tf-lang-l0 test`, `pnpm -F host-lite test`
- Bench (off-mode, if applicable): n/a
