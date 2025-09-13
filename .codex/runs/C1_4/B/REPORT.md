# REPORT — C1 — Run 4

## End Goal fulfillment
- EG-1: Shared exec path handles `/plan` and `/apply` via raw JSON handler and HTTP server wiring【F:packages/host-lite/src/server.ts†L93-L119】
- EG-2: Deterministic canonical outputs with per-world LRU capped at 32【F:packages/host-lite/src/server.ts†L9-L66】【F:packages/host-lite/tests/host-lite.test.ts†L11-L27】【F:packages/host-lite/tests/host-lite.test.ts†L96-L109】
- EG-3: Proofs gated by `DEV_PROOFS` with no work when disabled【F:packages/host-lite/src/server.ts†L57-L60】【F:packages/host-lite/tests/host-lite.test.ts†L29-L48】
- EG-4: Canonical 404/400 error bodies surfaced through raw handler【F:packages/host-lite/src/server.ts†L84-L119】【F:packages/host-lite/tests/host-lite.test.ts†L62-L83】
- EG-5: Package exports remain `src/server.ts`; imports clean and `.js`-suffixed【F:packages/host-lite/tests/host-lite.test.ts†L111-L139】【F:packages/host-lite/package.json†L1-L18】

## Blockers honored
- B-1: ✅ Deterministic in-memory host with LRU cap and canonical outputs【F:packages/host-lite/src/server.ts†L9-L66】【F:packages/host-lite/tests/host-lite.test.ts†L86-L109】
- B-2: ✅ Proof artifacts behind `DEV_PROOFS`; zero overhead when off【F:packages/host-lite/src/server.ts†L57-L60】【F:packages/host-lite/tests/host-lite.test.ts†L29-L48】

## Lessons / tradeoffs (≤5 bullets)
- Raw handler removes Node-specific parsing from tests.
- `import.meta.glob` enables file content checks without FS APIs.
- Cache map size check ensures per-world isolation.
- Updated glob options to silence deprecation warnings.
- Kept surface minimal and package exports unchanged.

## Bench notes (optional, off-mode)
- flag check: n/a
- no-op emit: n/a
