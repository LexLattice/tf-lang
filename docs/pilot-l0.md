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

The deterministic build pipeline lives under `scripts/pilot-build-run.mjs`. It parses the flow, emits canonical and manifest artifacts, generates the TypeScript runner, enforces a fixed clock, executes the generated runner, captures status/trace/summary outputs, and records canonical SHA-256 digests for every artifact. Golden copies are stored in `out/0.4/pilot-l0/golden/` for parity comparisons (not committed).

For a hand-authored baseline, `scripts/pilot-handwritten.mjs` invokes the in-memory adapters directly with the same deterministic clock. It emits mirrored artifacts to `out/0.4/pilot-l0/manual/` using the trace summary CLI. The `scripts/pilot-parity.mjs` harness hashes the generated and manual artifacts, producing `out/0.4/parity/report.json` and exiting non-zero if they diverge.

Run the full sequence with:

```sh
pnpm run pilot:all
cat out/0.4/parity/report.json
```
