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

Stages:

1. **Replay** — Start by emitting a metric signalling replay kickoff.
2. **Execution** — Publish a simple order payload on the `orders` topic, followed by a metric confirming the send.
3. **Ledger** — Write the fulfillment status to the ledger resource and emit a final metric capturing the ledger write.

## How to run

```sh
node scripts/pilot-min.mjs
cat out/0.4/pilot-l0/status.json
cat out/0.4/pilot-l0/summary.json
```

The run produces IR, canonical form, manifest, generated TypeScript, capability manifest, execution status, trace, and a summarized view. Capability gating requires the following effects: `Network.Out`, `Storage.Write`, `Observability`, and `Pure`, with writes permitted under the `res://ledger/` and `res://kv/` prefixes.
