# COMPLIANCE — C1 — Run WIN

## Blockers (must all be ✅)
- [x] No kernel/tag-schema changes
- [x] No per-call locks on host hot paths
- [x] No `static mut` / `unsafe` (Rust) introduced
- [x] No `as any` in TypeScript host code
- [x] ESM internal imports include `.js`
- [x] Tests run in parallel; no cross-test state bleed
- [x] Deterministic outputs (canonical JSON bytes & hashes where relevant)
- [x] In-memory only (no filesystem/DB/network persistence beyond HTTP)
- [x] Only `/plan` and `/apply` routes exist
- [x] Proof artifacts gated behind `DEV_PROOFS=1`

## Acceptance (oracle)
- [x] Idempotency: two identical POSTs for `/plan` and `/apply` → byte-identical responses; no extra effects
- [x] Canonicalization: journal entries serialize to canonical JSON with stable ordering/hashes
- [x] Proof gating: with `DEV_PROOFS=1` → proofs present; otherwise → absent
- [x] Isolation: static/dynamic checks confirm no persistence beyond the HTTP interface

## Evidence
- Code: `packages/host-lite/src/server.ts`, `packages/host-lite/src/canonical.ts`
- Tests: `packages/host-lite/test/c1.idempotency.test.ts`, `c1.canonical.test.ts`, `c1.proofs-gated.test.ts`, `c1.ephemeral.test.ts`
- CI runs: (attach latest job URLs)
- Notes: `.codex/tasks/*/BLOCKERS.yml` typo fixed post-run to satisfy blocker-lint; rule semantics unchanged.
