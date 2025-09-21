# Pilot L0 Flow

This pilot flow sketches a minimal replay → exec → ledger sequence using only the existing DSL primitives. The `pilot_min` flow emits metrics to mark the replay start, publishes a single order message, records execution sent, writes a ledger entry, and records the ledger write.

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

## How to run

```
node scripts/pilot-min.mjs
cat out/0.4/pilot-l0/status.json
cat out/0.4/pilot-l0/summary.json
```

The generated artifacts also include the IR (`pilot_min.ir.json`), canonical form (`pilot_min.canon.json`), manifest (`pilot_min.manifest.json`), trace (`trace.jsonl`), and generated TypeScript (`out/0.4/pilot-l0/codegen-ts/pilot_min`).

## Capability requirements

The run requires the following capabilities:

- `Network.Out`
- `Storage.Write`
- `Observability`
- `Pure`

Writes are allowed under the `res://ledger/` prefix. The generated manifest also declares a seed footprint under `res://kv/`, so
the provided caps file permits both prefixes.
