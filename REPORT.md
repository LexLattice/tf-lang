# REPORT — C1 — Run 2

## Targeted Goals
- Packaging clarity: host exists as a leaf package exposing only `POST /plan` and `POST /apply`; other paths return 404【F:packages/host-lite/src/index.ts†L15-L22】【F:packages/host-lite/src/index.ts†L76-L78】
- Canonical determinism: responses and proofs derive from `canonicalJsonBytes`, ensuring byte-stable output【F:packages/host-lite/src/index.ts†L24-L41】【F:packages/host-lite/src/index.ts†L44-L67】
- Idempotency without growth: `apply` caches only the last request per world, preventing cache expansion【F:packages/host-lite/src/index.ts†L44-L67】【F:packages/host-lite/tests/host-lite.test.ts†L75-L82】
- Proof gating: proof hashes computed only when `DEV_PROOFS=1`【F:packages/host-lite/src/index.ts†L35-L38】【F:packages/host-lite/src/index.ts†L60-L63】
- Test hardening: explicit 404 handling and hermetic tests using in-memory `Request` objects【F:packages/host-lite/src/index.ts†L76-L78】【F:packages/host-lite/tests/host-lite.test.ts†L67-L73】
- Dependency slim: runtime uses only Node built-ins; Fastify removed.
- Public boundaries only: host consumes `DummyHost` via new public export【F:packages/tf-lang-l0-ts/src/index.ts†L6-L9】

## Memory approach
Caching retains only the most recent `apply` result per world, replacing prior entries so a sequence of distinct requests leaves cache size constant【F:packages/host-lite/src/index.ts†L44-L67】【F:packages/host-lite/tests/host-lite.test.ts†L75-L82】

## Tests
- `pnpm build`
- `pnpm test`
