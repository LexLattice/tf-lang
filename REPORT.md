# REPORT — C1 — Run 2

## Targeted Goals
- TG-1: Host lives only in `packages/host-lite` and serves just `/plan` and `/apply`【F:packages/host-lite/src/server.ts†L11-L55】
- TG-2: Canonical JSON and hashing delegated to `tf-lang-l0`; repeat calls are byte-identical【F:packages/host-lite/src/server.ts†L39-L46】【F:packages/host-lite/tests/host-lite.test.ts†L11-L20】
- TG-3: Idempotent cache bounded to 16 entries preventing unbounded growth【F:packages/host-lite/src/server.ts†L46-L49】【F:packages/host-lite/tests/host-lite.test.ts†L63-L68】
- TG-4: Proofs emitted only when `DEV_PROOFS=1`; otherwise no hashing cost【F:packages/host-lite/src/server.ts†L41-L43】【F:packages/host-lite/tests/host-lite.test.ts†L22-L41】
- TG-5: Explicit 404 for non-endpoints with canonical body【F:packages/host-lite/src/server.ts†L15-L18】【F:packages/host-lite/tests/host-lite.test.ts†L56-L60】
- TG-6: Runtime uses no third-party HTTP framework; built on `node:http`【F:packages/host-lite/src/server.ts†L1】
- TG-7: No deep cross-package imports; `DummyHost` exported publicly【F:packages/tf-lang-l0-ts/src/index.ts†L2-L9】【F:packages/host-lite/tests/host-lite.test.ts†L71-L74】

## Blockers honored
- B-1: ✅ Only `/plan` and `/apply` endpoints, in-memory state, deterministic output【F:packages/host-lite/src/server.ts†L11-L55】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with canonical serialization【F:packages/host-lite/tests/host-lite.test.ts†L22-L41】

## Lessons / tradeoffs (≤5 bullets)
- Dropping Fastify slimmed dependencies but required custom request handling.
- Exporting `DummyHost` opened minimal public surface for host integration.
- Bounded maps avoid memory growth at the cost of occasional cache eviction.
- Direct handler tests keep suite hermetic without network sockets.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
