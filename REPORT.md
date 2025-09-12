# REPORT — C1 — Run 2

## End Goal fulfillment
- EG-1: Minimal host exposes only `/plan` and `/apply` via Node HTTP【F:packages/host-lite/src/server.ts†L96-L101】
- EG-2: Idempotent, canonical responses with bounded cache【F:packages/host-lite/src/server.ts†L12-L66】【F:packages/host-lite/tests/host-lite.test.ts†L12-L25】【F:packages/host-lite/tests/host-lite.test.ts†L67-L74】
- EG-3: Journal entries canonical with proofs gated by `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】
- EG-4: State is in-memory and resets on new host creation【F:packages/host-lite/tests/host-lite.test.ts†L47-L56】
- EG-5: Non-endpoints return explicit 404 with canonical body【F:packages/host-lite/src/server.ts†L98-L101】【F:packages/host-lite/tests/host-lite.test.ts†L59-L65】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L92】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Node HTTP removed third-party runtime dependencies.
- LRU cache (32 entries/world) enforces idempotency without memory growth.
- Public export of `DummyHost` avoids deep relative imports.
- Direct handler testing keeps suite hermetic and parallel-safe.
- Canonicalization centralized through `tf-lang-l0` helpers.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
