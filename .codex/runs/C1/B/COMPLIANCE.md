# COMPLIANCE — C1 — Run 1

## Blockers (must all be ✅)
- [x] No changes to existing kernel semantics or tag schemas from A/B — code link: n/a (new service only).
- [x] No per-call locks on hot paths; no `static mut`/`unsafe`; no TS `as any` — code link: services/host-lite-ts/src/server.ts
- [x] ESM internal imports must include `.js` — code link: services/host-lite-ts/src/server.ts
- [x] Tests run in parallel without cross-test state bleed — test link: services/host-lite-ts/tests/host-lite.test.ts
- [x] Outputs must be deterministic (canonical JSON bytes & hashes where relevant) — code link: services/host-lite-ts/src/server.ts
- [x] Host must not use files or external DBs; in-memory only — code/test link: services/host-lite-ts/src/server.ts / tests/host-lite.test.ts
- [x] Only `/plan` and `/apply` endpoints are allowed — code link: services/host-lite-ts/src/server.ts
- [x] `/plan` and `/apply` must be idempotent — test link: services/host-lite-ts/tests/host-lite.test.ts
- [x] Proof artifacts must be gated behind `DEV_PROOFS=1` — test link: services/host-lite-ts/tests/host-lite.test.ts

## Acceptance
- [x] Idempotency: two identical `POST /plan` and `POST /apply` calls yield byte-identical responses and no extra effects — tests/host-lite.test.ts
- [x] Canonicalization: journal entries serialize to canonical JSON with stable ordering/hashes — tests/host-lite.test.ts
- [x] Proof gating: with `DEV_PROOFS=1` → proofs present; otherwise → absent — tests/host-lite.test.ts
- [x] Isolation: no filesystem/network persistence beyond the HTTP interface — tests/host-lite.test.ts

## Evidence
- Code: services/host-lite-ts/src/server.ts
- Tests: services/host-lite-ts/tests/host-lite.test.ts
- CI runs: `pnpm test`
- Bench (off-mode, if applicable): n/a
