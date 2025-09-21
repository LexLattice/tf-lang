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

The deterministic pilot build pipeline lives in `scripts/pilot-build-run.mjs`. It parses `examples/flows/pilot_min.tf`, emits the canonical artifacts, generates the TypeScript runner, executes it under a fixed clock, and records digests for the IR, canon, manifest, status, trace, and summary. Each run refreshes `out/0.4/pilot-l0/golden/` with the generated baseline.

`scripts/pilot-handwritten.mjs` replays the same flow by directly invoking the in-memory adapters, while `scripts/pilot-parity.mjs` compares the generated and manual artifacts via canonical SHA-256 hashes. Run the full suite with:

```sh
pnpm run pilot:all
cat out/0.4/parity/report.json
```

Both runners share a fixed millisecond clock configured through `TF_FIXED_TS` (default `1750000000000`). To force a reproducible end-to-end run:

```sh
TF_FIXED_TS=1750000000000 pnpm run pilot:all && cat out/0.4/parity/report.json
```

The parity harness exits non-zero if any artifact digests differ and is covered by `tests/pilot-parity.test.mjs`, which reruns the harness to ensure byte-for-byte determinism.

## Full pilot parity

The end-to-end pilot parity harness compares the T5 (0.3) pipeline against the L0-generated flow on a tiny replay slice. Run the full parity cycle with:

```sh
TF_PILOT_FULL=1 node scripts/t5-build-run.mjs \
  && TF_PILOT_FULL=1 node scripts/pilot-full-build-run.mjs \
  && node scripts/pilot-full-parity.mjs
cat out/0.4/parity/full/report.json | jq .
```

When the outputs match, `out/0.4/parity/full/report.json` records identical hashes for `frames`, `orders`, `fills`, and `state` along with `"equal": true`.

### Runtime verify (schema + meta + composition)
- Local: `node scripts/runtime-verify.mjs --flow pilot --out out/0.4/verify/pilot/report.json --catalog out/0.4/pilot-l0/catalog.json --catalog-hash $(jq -r '.provenance.catalog_hash' out/0.4/pilot-l0/status.json)`
  - Add `--print-inputs` to echo the resolved artifact paths + hashes.
  - The report now includes an `inputs` map containing `{path, sha256}` for each artifact (IR, manifest, status, trace, catalog).
- CI: workflow **“L0 Runtime Verify”** runs the same steps and uploads `l0-runtime-verify` artifacts.
