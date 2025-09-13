# REPORT — C1 — Run 2

## End Goal fulfillment
- EG-1: Leaf package `host-lite` exposes only `POST /plan` and `POST /apply` via built-in HTTP handler【F:packages/host-lite/src/index.ts†L27-L64】
- EG-2: Repeated calls are idempotent and canonical; state resets on new host【F:packages/host-lite/tests/host-lite.test.ts†L11-L20】【F:packages/host-lite/tests/host-lite.test.ts†L45-L55】
- EG-3: Journal entries are canonical with proofs gated behind `DEV_PROOFS`【F:packages/host-lite/src/index.ts†L52-L57】【F:packages/host-lite/tests/host-lite.test.ts†L22-L43】

## Targeted goals
- TG-1 Packaging clarity: single leaf package with two routes【F:packages/host-lite/src/index.ts†L27-L64】
- TG-2 Canonical determinism centralized via L0 helpers【F:packages/host-lite/src/index.ts†L33-L59】
- TG-3 Idempotency without growth: bounded cache limits worlds and entries【F:packages/host-lite/src/index.ts†L12-L21】【F:packages/host-lite/tests/host-lite.test.ts†L65-L72】
- TG-4 Proof gating intact: proofs emitted only when `DEV_PROOFS=1`【F:packages/host-lite/src/index.ts†L55-L57】【F:packages/host-lite/tests/host-lite.test.ts†L22-L43】
- TG-5 Test hardening: 404 for non-endpoints and hermetic tests【F:packages/host-lite/src/index.ts†L27-L31】【F:packages/host-lite/tests/host-lite.test.ts†L57-L63】
- TG-6 Dependency slim: no third-party HTTP framework, only built-ins【F:packages/host-lite/package.json†L1-L18】
- TG-7 Public boundaries only: host imports through `tf-lang-l0` export surface【F:packages/host-lite/src/index.ts†L1】【F:packages/tf-lang-l0-ts/src/index.ts†L2-L9】【F:packages/tf-lang-l0-ts/package.json†L1-L8】

## Blockers honored
- B-1: ✅ Only `/plan` and `/apply`, in-memory state, deterministic outputs【F:packages/host-lite/src/index.ts†L27-L64】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS`, no per-call locks or `as any`【F:packages/host-lite/src/index.ts†L55-L57】

## Lessons / tradeoffs (≤5 bullets)
- Bounded caches prevent unbounded memory growth while preserving idempotency.
- Removing Fastify reduced dependency surface but required custom routing logic.
- Exporting `DummyHost` enabled public boundary adherence.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
