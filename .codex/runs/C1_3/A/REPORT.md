# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Minimal host exposes only `POST /plan` and `POST /apply` with canonical error handling【F:packages/host-lite/src/server.ts†L96-L116】【F:packages/host-lite/tests/host-lite.test.ts†L63-L77】
- EG-2: Responses and journals are byte-identical on repeats and proofs gate on `DEV_PROOFS`【F:packages/host-lite/src/server.ts†L55-L61】【F:packages/host-lite/tests/host-lite.test.ts†L12-L48】
- EG-3: State is ephemeral; per-world cache capped at 32 entries (LRU) across worlds【F:packages/host-lite/src/server.ts†L9-L36】【F:packages/host-lite/tests/host-lite.test.ts†L87-L99】

## Blockers honored
- B-1: ✅ In-memory only; deterministic canonical outputs; endpoints restricted【F:packages/host-lite/src/server.ts†L38-L132】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` with zero overhead when disabled【F:packages/host-lite/src/server.ts†L55-L61】

## Lessons / tradeoffs (≤5 bullets)
- Added raw handler to expose 400 errors without opening sockets.
- Multi-world cache test proves per-world LRU bound.
- Export added for tests but remains within package boundary.
- Node `http` keeps runtime dependencies minimal.
- Canonicalization centralized via `tf-lang-l0` utilities.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
