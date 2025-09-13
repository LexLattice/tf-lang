# REPORT — C1 — Run 4

## Goal → Evidence map
- G1 Raw path unified; `createServer` delegates to `makeRawHandler`【F:packages/host-lite/src/server.ts:93】【F:packages/host-lite/src/server.ts:106】
- G2 Endpoints only POST `/plan` and `/apply`; otherwise 404【F:packages/host-lite/src/server.ts:84】【F:packages/host-lite/test/c1.http-400-404.test.ts:6】
- G3 Determinism: `/plan` and `/apply` produce byte-identical responses【F:packages/host-lite/test/c1.byte-determinism.test.ts:7】
- G4 Proof gating: DEV_PROOFS toggles tags; count check【F:packages/host-lite/src/server.ts:58】【F:packages/host-lite/test/c1.proofs-gating-count.test.ts:6】
- G5 LRU bounds: per-world cap 32; map size equals worlds touched【F:packages/host-lite/src/server.ts:9】【F:packages/host-lite/test/c1.lru-multiworld.test.ts:4】
- G6 Hygiene: ESM internal `.js`; public exports only; no deep imports【F:packages/host-lite/test/c1.import-hygiene.test.ts:1】
- G7 Packaging: `main` and `exports` both `src/server.ts`【F:packages/host-lite/package.json:7】

## Notes & tradeoffs
- Centralized parsing simplifies server wiring and ensures canonical error bodies.
- Shared `exec` path guarantees identical planning/apply response shapes and bytes.
- LRU scoped per world prevents cross-world interference and growth.

## Determinism runs
- Repeated `pnpm -F host-lite-ts test` stable across 5 runs (documented in OBS_LOG.md).
