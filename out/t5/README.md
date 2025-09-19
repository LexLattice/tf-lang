# T5 Sprint 1 – Reproducibility Guide

## Build

```
node node_modules/typescript/lib/tsc.js -p out/t5/pilot-core/tsconfig.json
node node_modules/typescript/lib/tsc.js -p out/t5/pilot-replay/tsconfig.json
node node_modules/typescript/lib/tsc.js -p out/t5/pilot-strategy/tsconfig.json
node node_modules/typescript/lib/tsc.js -p out/t5/pilot-risk/tsconfig.json
```

## Risk Unit Test

```
node out/t5/pilot-risk/dist/index.test.js
```

## Replay Generation

```
node out/t5/pilot-replay/dist/cli.js --input out/t5/tests/data/ticks-mini.csv --seed 42 --slice 0:50:1 --out out/t5/replay/frames.ndjson
```

## Strategy Orders

Momentum:
```
node out/t5/pilot-strategy/dist/cli.js --strategy momentum --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders.ndjson
```

Mean Reversion:
```
node out/t5/pilot-strategy/dist/cli.js --strategy meanReversion --frames out/t5/replay/frames.ndjson --seed 42 --out out/t5/effects/orders-mean-reversion.ndjson
```

## Hash Validation

```
sha256sum out/t5/replay/frames.ndjson out/t5/effects/orders.ndjson out/t5/effects/orders-mean-reversion.ndjson
```
