# REPORT — C1 — Run 1

## End Goal fulfillment
- EG-1: Minimal HTTP host with only `POST /plan` and `POST /apply` providing idempotent, ephemeral world operations — services/host-lite-ts/src/server.ts
- EG-2: Canonical journal entries with proofs gated by `DEV_PROOFS` — services/host-lite-ts/tests/host-lite.test.ts

## Blockers honored
- B-1: ✅ Only `/plan` and `/apply` endpoints; no external persistence — services/host-lite-ts/src/server.ts
- B-2: ✅ Deterministic canonical outputs; proofs behind env flag — services/host-lite-ts/tests/host-lite.test.ts

## Lessons / tradeoffs (≤5 bullets)
- Runtime environment checks enable flexible proof gating.
- Stateless design simplifies idempotency.
- Canonical JSON helpers avoid ordering drift.
- Using built-in `http` keeps dependencies minimal.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
