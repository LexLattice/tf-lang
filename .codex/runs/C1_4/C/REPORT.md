# REPORT — C1 — Run 4

## End Goal fulfillment
- EG-1: Minimal host exposes only `POST /plan` and `POST /apply` with raw JSON handler【F:packages/host-lite/src/server.ts†L88-L108】
- EG-2: Canonical, byte-identical responses with per-world LRU cache【F:packages/host-lite/src/server.ts†L13-L70】【F:packages/host-lite/tests/host-lite.test.ts†L30-L44】【F:packages/host-lite/tests/host-lite.test.ts†L87-L101】
- EG-3: Proofs gated by `DEV_PROOFS` with no extra hashing when off【F:packages/host-lite/src/server.ts†L62-L64】【F:packages/host-lite/tests/host-lite.test.ts†L46-L60】
- EG-4: Canonical 404/400 errors for bad routes, methods, and JSON【F:packages/host-lite/src/server.ts†L88-L108】【F:packages/host-lite/tests/host-lite.test.ts†L62-L73】
- EG-5: State remains in-memory and resets per host instance【F:packages/host-lite/tests/host-lite.test.ts†L75-L85】

## Blockers honored
- B-1: ✅ Deterministic in-memory host with LRU cap 32 and map-size match【F:packages/host-lite/src/server.ts†L13-L40】【F:packages/host-lite/tests/host-lite.test.ts†L87-L101】
- B-2: ✅ Proof artifacts only when `DEV_PROOFS=1`; hashing skipped otherwise【F:packages/host-lite/src/server.ts†L62-L64】【F:packages/host-lite/tests/host-lite.test.ts†L46-L60】

## Lessons / tradeoffs (≤5 bullets)
- Raw handler removed need for socket-based tests.
- Mocked hashing verified zero-cost proof gating.
- Import sweep constrained to source to avoid false positives.
- Multi-world cache tracked both per-world cap and map size.
- Canonicalization centralized in single exec path.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
