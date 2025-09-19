# T5 Sprint 1 Rerun Commands

## Build & Test
```
pnpm --filter @tf-lang/pilot-core build
pnpm --filter @tf-lang/pilot-core test
pnpm --filter @tf-lang/pilot-replay build
pnpm --filter @tf-lang/pilot-replay test
pnpm --filter @tf-lang/pilot-strategy build
pnpm --filter @tf-lang/pilot-strategy test
pnpm --filter @tf-lang/pilot-risk build
pnpm --filter @tf-lang/pilot-risk test
```

## Artifact Generation
```
node packages/pilot-replay/dist/cli.js replay --input tests/data/ticks-mini.csv --seed 42 --slice 0:50:1 --out out/t5/replay/frames.ndjson
node packages/pilot-strategy/dist/cli.js run --strategy momentum --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders-momentum.ndjson
node packages/pilot-strategy/dist/cli.js run --strategy meanReversion --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders.ndjson
```
