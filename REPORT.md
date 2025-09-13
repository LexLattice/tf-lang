# REPORT — C1 — Run 3

## End Goal fulfillment
- EG-1: Minimal host exposes only `/plan` and `/apply` via Node HTTP【F:packages/host-lite/src/server.ts†L74-L83】
- EG-2: Canonical, idempotent responses with bounded per-world cache【F:packages/host-lite/src/server.ts†L20-L71】【F:packages/host-lite/tests/host-lite.test.ts†L13-L44】【F:packages/host-lite/tests/host-lite.test.ts†L81-L99】
- EG-3: Proofs gated by `DEV_PROOFS` with no cost when off【F:packages/host-lite/src/server.ts†L49-L53】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】
- EG-4: Error model returns canonical 404/400 bodies【F:packages/host-lite/src/server.ts†L85-L110】【F:packages/host-lite/tests/host-lite.test.ts†L59-L76】【F:packages/host-lite/tests/host-lite.test.ts†L100-L113】
- EG-5: State stays in-memory and resets on new host creation【F:packages/host-lite/tests/host-lite.test.ts†L47-L56】

## Blockers honored
- B-1: ✅ Deterministic in-memory host with LRU cache cap 32【F:packages/host-lite/src/server.ts†L10-L37】【F:packages/host-lite/tests/host-lite.test.ts†L81-L99】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS` gated; zero overhead when disabled【F:packages/host-lite/src/server.ts†L49-L53】【F:packages/host-lite/tests/host-lite.test.ts†L26-L44】

## Lessons / tradeoffs (≤5 bullets)
- Node HTTP only; no new runtime deps.
- Cache cap 32 balances determinism and memory; multi-world test proves bound.
- Parsing moved to handler to surface 400s without sockets.
- Boundary scan limited to package to avoid repo-wide false positives.
- Canonicalization centralized in single exec path.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
