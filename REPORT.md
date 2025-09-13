# REPORT — C1 — Run 4

## End Goal fulfillment
- EG-1: Raw handler enforces JSON parsing and routes only `/plan` and `/apply`【F:packages/host-lite/src/server.ts†L84-L104】
- EG-2: Canonical, idempotent responses with per-world LRU cache【F:packages/host-lite/src/server.ts†L13-L66】【F:packages/host-lite/tests/host-lite.test.ts†L24-L34】【F:packages/host-lite/tests/host-lite.test.ts†L92-L105】
- EG-3: Proofs gated by `DEV_PROOFS` with no overhead when off【F:packages/host-lite/src/server.ts†L57-L60】【F:packages/host-lite/tests/host-lite.test.ts†L36-L55】
- EG-4: Canonical 404/400 error bodies via raw handler【F:packages/host-lite/src/server.ts†L84-L104】【F:packages/host-lite/tests/host-lite.test.ts†L57-L68】
- EG-5: Package remains ESM with explicit export checks【F:packages/host-lite/package.json†L1-L18】【F:packages/host-lite/tests/host-lite.test.ts†L107-L127】

## Blockers honored
- B-1: ✅ Deterministic in-memory host with per-world LRU cap 32【F:packages/host-lite/src/server.ts†L13-L36】【F:packages/host-lite/tests/host-lite.test.ts†L82-L105】
- B-2: ✅ Proof artifacts appear only when `DEV_PROOFS=1`【F:packages/host-lite/src/server.ts†L57-L60】【F:packages/host-lite/tests/host-lite.test.ts†L36-L55】

## Lessons / tradeoffs (≤5 bullets)
- Centralized JSON parsing simplified tests and server wiring.
- Deep import sweep restricted to package to avoid cross-repo noise.
- Cache map size check confirmed multi-world isolation.
- Using package name in tests avoided deep import violations.
- Canonical bytes derived once per exec for determinism.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
