# Observation Log — C1 — Run 4

- Strategy: Keep unified raw path; delegate `createServer` → `makeRawHandler`; share `exec(world, plan)` for both routes; enforce canonical errors.
- Key changes: packages/host-lite/src/server.ts; packages/host-lite/test/*; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism runs: 5× `pnpm -F host-lite-ts test` (parallel) — all green, identical outputs.
 - Determinism runs: 5× `pnpm -r test` executed in parallel — all green.
- Tradeoffs: Did not split handlers into multiple source files to avoid churn; imports remain via public `tf-lang-l0` exports; no new deps.
- Proof gating: Explicit count check in tests; zero overhead when off (no proof fields computed/emitted).
