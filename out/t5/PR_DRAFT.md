# Draft PR: T5 Sprint 1

## Summary
- scaffolded `@tf-lang/pilot-core` with canonical schemas, zod validators, and deterministic helpers (seeded RNG, number/frame normalization, minor unit conversion).
- added replay CLI/package to canonicalise CSV ticks into sorted NDJSON frames with deterministic slicing and schema validation.
- delivered strategy package with momentum and mean-reversion engines plus CLI for producing deterministic order streams.
- stubbed pilot-risk evaluator with schema-validated passthrough and coverage.
- recorded deterministic artifacts under `out/t5/` along with rerun commands and sprint status metadata.

## Testing
- `pnpm --filter @tf-lang/pilot-core build`
- `pnpm --filter @tf-lang/pilot-core test`
- `pnpm --filter @tf-lang/pilot-replay build`
- `pnpm --filter @tf-lang/pilot-replay test`
- `pnpm --filter @tf-lang/pilot-strategy build`
- `pnpm --filter @tf-lang/pilot-strategy test`
- `pnpm --filter @tf-lang/pilot-risk build`
- `pnpm --filter @tf-lang/pilot-risk test`
- `node packages/pilot-replay/dist/cli.js replay --input tests/data/ticks-mini.csv --seed 42 --slice 0:50:1 --out out/t5/replay/frames.ndjson`
- `node packages/pilot-strategy/dist/cli.js run --strategy momentum --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders-momentum.ndjson`
- `node packages/pilot-strategy/dist/cli.js run --strategy meanReversion --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders.ndjson`
- `pnpm -w -r build`

## Next Steps
- flesh out pilot-risk to compute exposure metrics (T5.4+).
- integrate replay/strategy outputs into a combined evaluation harness.
