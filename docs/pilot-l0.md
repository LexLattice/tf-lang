# Pilot L0 Flow Sketch

This pilot sketch walks through a minimal replay → exec → ledger sequence using the existing TF primitives.

```
seq{
  emit-metric(name="pilot.replay.start");
  publish(topic="orders", key="o-1", payload="{\"sym\":\"ABC\",\"side\":\"buy\",\"qty\":1}");
  emit-metric(name="pilot.exec.sent");
  write-object(uri="res://ledger/pilot", key="o-1", value="filled");
  emit-metric(name="pilot.ledger.write")
}
```

## Stages

- **Replay** — `emit-metric` announces the replay start (`pilot.replay.start`).
- **Exec** — `publish` forwards an `orders` topic message for key `o-1` and records the dispatch via `emit-metric` (`pilot.exec.sent`).
- **Ledger** — `write-object` records the fill result under `res://ledger/pilot`, followed by a final `emit-metric` (`pilot.ledger.write`).

## How to Run

```
node scripts/pilot-min.mjs
cat out/0.4/pilot-l0/status.json
cat out/0.4/pilot-l0/summary.json
```

The capability guard needs `Network.Out`, `Storage.Write`, `Observability`, and `Pure`, with writes allowed under `res://ledger/`.
