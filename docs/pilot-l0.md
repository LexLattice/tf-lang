# Pilot L0 Flow

This pilot sketch uses existing DSL primitives to illustrate a minimal replay → execution → ledger write pipeline.

## Flow overview

The flow defined in `examples/flows/pilot_min.tf` emits a start metric, publishes an order message, records an execution metric, writes a ledger entry, and finishes with a ledger metric. It only uses string and numeric arguments to stay within the minimal DSL surface.

## Running the pilot

```sh
node scripts/pilot-min.mjs
cat out/0.4/pilot-l0/status.json
cat out/0.4/pilot-l0/summary.json
```

The runner script creates IR, canonical form, and manifest artifacts, generates TypeScript code, produces capability gates, and executes the generated flow. Status and trace data are written under `out/0.4/pilot-l0/`.

## Capabilities

Execution requires the following capabilities:

- `Network.Out`
- `Storage.Write`
- `Observability`
- `Pure`

Writes are allowed for resources prefixed by `res://ledger/` and `res://kv/`.
