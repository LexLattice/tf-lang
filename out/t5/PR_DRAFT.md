## Summary
- add pilot-core schema definitions, validation helpers, and deterministic numeric utilities for the T5 sprint
- scaffold replay CLI to transform CSV ticks into canonical NDJSON frames and produce reproducible hashes
- implement momentum and mean-reversion strategies plus risk stub, including deterministic order emission and validation scripts

## Testing
- node node_modules/typescript/lib/tsc.js -p out/t5/pilot-core/tsconfig.json
- node node_modules/typescript/lib/tsc.js -p out/t5/pilot-replay/tsconfig.json
- node node_modules/typescript/lib/tsc.js -p out/t5/pilot-strategy/tsconfig.json
- node node_modules/typescript/lib/tsc.js -p out/t5/pilot-risk/tsconfig.json
- node out/t5/pilot-risk/dist/index.test.js
- node out/t5/pilot-replay/dist/cli.js --input out/t5/tests/data/ticks-mini.csv --seed 42 --slice 0:50:1 --out out/t5/replay/frames.ndjson
- node out/t5/pilot-strategy/dist/cli.js --strategy momentum --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders.ndjson
- node out/t5/pilot-strategy/dist/cli.js --strategy meanReversion --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders-mean-reversion.ndjson
- node out/t5/validate-artifacts.js
- pnpm -w -r build (fails: adapter-legal-ts build script in workspace)
