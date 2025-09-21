# Pilot L0 Flow Sketch

This pilot demonstrates a minimal replay → execution → ledger flow using only existing DSL primitives.

## Flow

```
seq{
  emit-metric(name="pilot.replay.start");
  publish(topic="orders", key="o-1", payload="{\"sym\":\"ABC\",\"side\":\"buy\",\"qty\":1}");
  emit-metric(name="pilot.exec.sent");
  write-object(uri="res://ledger/pilot", key="o-1", value="filled");
  emit-metric(name="pilot.ledger.write")
}
```

Legend:

- `publish` → Exec wire-out
- `write-object` → Ledger write
- `emit-metric` → Observability hooks

Stages:

1. **Replay** — Start by emitting a metric signalling replay kickoff.
2. **Execution** — Publish a simple order payload on the `orders` topic, followed by a metric confirming the send.
3. **Ledger** — Write the fulfillment status to the ledger resource and emit a final metric capturing the ledger write.

## How to run

```sh
pnpm -w -r build
node scripts/pilot-min.mjs
cat out/0.4/pilot-l0/status.json
cat out/0.4/pilot-l0/summary.json
```

The run produces IR, canonical form, manifest, generated TypeScript, capability manifest, execution status, trace, and a summarized view. Capability gating requires the following effects: `Network.Out`, `Storage.Write`, `Observability`, and `Pure`, with writes permitted under the `res://ledger/` prefix.

## Parity harness

A deterministic build harness is available via:

```sh
pnpm run pilot:build-run
pnpm run pilot:manual
pnpm run pilot:parity
```

The `pilot:build-run` script parses the flow, regenerates the TypeScript runner, executes it with a fixed clock, and materializes status, trace, summary, and digest artifacts under `out/0.4/pilot-l0/`. The `pilot:manual` script replays the same effects using the in-memory adapters to produce a minimal handwritten baseline. `pilot:parity` compares the generated and handwritten artifacts and fails fast when any digest diverges.

To run the full loop in one go use:

```sh
pnpm run pilot:all
```
