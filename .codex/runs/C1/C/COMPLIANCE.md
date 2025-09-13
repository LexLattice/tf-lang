# COMPLIANCE — C1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code only adds an HTTP host.
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — `http-lite.ts` uses simple Maps without casts.
- [x] ESM internal imports must include `.js` — see imports in `http-lite.ts`.
- [x] Tests run in parallel without cross-test state bleed — each test spins up its own server.
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — responses built via `canonicalJsonBytes`.
- [x] Host must not use files or external DBs; in-memory only — worlds stored in `Map`.
- [x] Only `/plan` and `/apply` endpoints are allowed — other paths return `404`.
- [x] `/plan` and `/apply` must be idempotent — responses cached by request hash.
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — proofs included only when flag enabled.

## Acceptance (oracle)
- [x] Idempotency: repeat calls yield byte-identical responses and no extra effects — `host-lite.test.ts`.
- [x] Canonicalization: journal entries serialize to canonical JSON — `host-lite.test.ts`.
- [x] Proof gating: proofs present only with `DEV_PROOFS=1` — `host-lite.test.ts`.
- [x] Isolation: world state resets on restart; no external persistence — `host-lite.test.ts`.

## Evidence
- Code: `packages/tf-lang-l0-ts/src/host/http-lite.ts`
- Tests: `packages/tf-lang-l0-ts/tests/host-lite.test.ts`
- CI runs: `pnpm test`
- Bench (off-mode, if applicable): n/a
