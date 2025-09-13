# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Host packaged only in `packages/host-lite` with `/plan` and `/apply` routes【F:packages/host-lite/src/server.ts†L96-L101】【F:packages/host-lite/package.json†L2-L9】
- EG-2: Canonical deterministic responses via L0 helpers【F:packages/host-lite/src/server.ts†L45-L66】【F:packages/host-lite/tests/host-lite.test.ts†L12-L24】
- EG-3: Journal proofs gated behind `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】
- EG-4: Per-world LRU cache (cap 32) preserves idempotency without growth【F:packages/host-lite/src/server.ts†L9-L36】【F:packages/host-lite/tests/host-lite.test.ts†L75-L97】
- EG-5: HTTP parser yields canonical 400/404 errors【F:packages/host-lite/src/server.ts†L105-L118】【F:packages/host-lite/tests/host-lite.test.ts†L59-L73】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L139】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Default cache cap 32 balances replay speed with bounded memory; tested across multiple worlds.
- Centralized `handleHttp` avoids framework deps and ensures uniform error bodies.
- Package exports point to `dist/` to stay aligned with `tf-lang-l0` packaging.
- Tests stay hermetic by invoking handlers directly—no sockets or FS writes.
- Only runtime dep remains `tf-lang-l0`; Node `http` covers transport.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
