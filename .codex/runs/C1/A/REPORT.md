# REPORT — C1 — Run 1

## End Goal fulfillment
- EG-1: In-memory Fastify host exposes only `/plan` and `/apply` endpoints【F:services/host-lite/src/server.ts†L17-L78】
- EG-2: Identical `POST /plan` and `POST /apply` calls return byte-identical responses【F:services/host-lite/tests/host-lite.test.ts†L10-L18】
- EG-3: Journal entries are canonical with proofs gated by `DEV_PROOFS`【F:services/host-lite/src/server.ts†L31-L36】【F:services/host-lite/tests/host-lite.test.ts†L22-L42】
- EG-4: World state resets on restart, ensuring ephemerality【F:services/host-lite/tests/host-lite.test.ts†L47-L58】

## Blockers honored
- B-1: ✅ Only `/plan` and `/apply` endpoints, in-memory state, and idempotent caching【F:services/host-lite/src/server.ts†L17-L78】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` and deterministic canonical outputs【F:services/host-lite/tests/host-lite.test.ts†L22-L42】

## Lessons / tradeoffs (≤5 bullets)
- Canonical response caching ensures byte-level idempotency.
- Relative workspace imports required for unexported modules.
- Double JSON parsing trades speed for determinism.
- Fastify.inject enables isolation without network sockets.
- Environment flag toggles proof emission for development only.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
