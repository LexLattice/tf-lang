# Observation Log — C1 — Run WIN

- Strategy chosen: Base on Run A semantics; keep host as a leaf package; centralize canonicalization; request injection for tests.
- Key changes (files): `packages/host-lite/src/server.ts`, `src/canonical.ts`, tests under `packages/host-lite/test/*`.
- Determinism stress (runs × passes): 5 × parallel TS suite — stable; idempotency snapshots identical across runs.
- Near-misses vs blockers: None in code. Post-run fix to `BLOCKERS.yml` was a **typo correction** from `main`, not a rule change.
- Notes: Optional dep trim (Fastify → Node `http`) is feasible later without changing semantics; current form passes all acceptance checks.
