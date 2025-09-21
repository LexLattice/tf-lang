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

For deterministic build + parity validation:

```sh
pnpm run pilot:all
cat out/0.4/parity/report.json
```

`scripts/pilot-build-run.mjs` rebuilds the pilot flow end-to-end (IR, canon, manifest, TypeScript codegen, capability caps) then executes the generated runner with a deterministic clock. It emits status, trace, summary, and digest hashes plus a golden snapshot under `out/0.4/pilot-l0/golden/` for later comparison.

`scripts/pilot-handwritten.mjs` replays the same flow directly against the in-memory adapters. It uses the same deterministic clock, writes artifacts under `out/0.4/pilot-l0/manual/`, and relies on the shared `trace-summary` CLI for reporting.

`scripts/pilot-parity.mjs` compares the generated and manual artifacts by hashing each JSON / JSONL payload (via `scripts/hash-jsonl.mjs`). On mismatch it reports the differing digests and exits with a non-zero status.
