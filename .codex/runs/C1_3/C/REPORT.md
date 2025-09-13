# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Minimal host exposes only `/plan` and `/apply` via Node HTTP【F:packages/host-lite/src/server.ts†L96-L104】
- EG-2: Idempotent, canonical responses with bounded cache【F:packages/host-lite/src/server.ts†L12-L66】【F:packages/host-lite/tests/host-lite.test.ts†L12-L25】【F:packages/host-lite/tests/host-lite.test.ts†L76-L90】
- EG-3: Journal entries canonical with proofs gated by `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L27-L46】
- EG-4: State is in-memory and resets on new host creation【F:packages/host-lite/tests/host-lite.test.ts†L48-L56】
- EG-5: Error paths return canonical bodies: 404 for unknown routes, 400 for bad JSON【F:packages/host-lite/src/server.ts†L96-L104】【F:packages/host-lite/src/server.ts†L112-L125】【F:packages/host-lite/tests/host-lite.test.ts†L60-L74】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L91】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Node HTTP keeps runtime deps slim (only `tf-lang-l0`).
- LRU cache (32 entries/world) prevents growth across multiple worlds.
- Optional body argument allowed hermetic 400 tests without sockets.
- Package export clarifies boundary; no deep relative imports.
- Canonicalization centralized through `tf-lang-l0` helpers.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
