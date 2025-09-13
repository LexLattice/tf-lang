# Observation Log — C1 — Run 4

- Strategy chosen: Introduced raw JSON handler to front all requests, tightening error paths and import hygiene.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts
- Determinism stress (runs × passes): 3×; stable outputs.
- Near-misses vs blockers: ensured test sweep skipped node_modules to avoid false positives.
- Notes: per-world LRU capped at 32 with map-sized to worlds touched; proofs hashed only when DEV_PROOFS=1.
