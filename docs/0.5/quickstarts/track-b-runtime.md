# Track B — Runtime & Composition Quickstart

Rebuild the pilot flow, generate the deterministic TypeScript runner, and confirm provenance hashes and trace output.

## Prerequisites

- Complete the Track A setup (catalog + IR)
- `PILOT_OUT_DIR` writeable (defaults to `out/0.5/pilot-l0` below)
- `jq` for inspecting JSON

## Commands (3–7 steps)

```bash
FLOW=examples/flows/pilot_min.tf
OUT=out/0.5/pilot-l0
PILOT_OUT_DIR="$OUT" pnpm run pilot:build-run
jq '{ok, ops, effects}' "$OUT/status.json"
head -n 1 "$OUT/trace.jsonl"
node scripts/validate-trace.mjs --require-meta \
  --ir "$(jq -r .provenance.ir_hash "$OUT/status.json")" \
  --manifest "$(jq -r .provenance.manifest_hash "$OUT/status.json")" \
  --catalog "$(jq -r .provenance.catalog_hash "$OUT/status.json")" \
  < "$OUT/trace.jsonl"
```

## Expected output

```
{"ok":true,"ops":5,"effects":["Network.Out","Observability","Storage.Write"]}
{"ts":1750000000000,"prim_id":"tf:observability/emit-metric@1",...}
{"invalid":0,"meta_checked":true,"ok":true,"total":5}
```

*The pilot script stamps fixed timestamps and hashes so reruns match byte-for-byte. Generated runners live under `out/0.5/pilot-l0/codegen-ts/` with patched manifests.*

## Where next?

- Runtime adapters & provenance: [`docs/pilot-l0.md`](../../pilot-l0.md)
- Trace schema & parity harness: [`docs/trace-schema.md`](../../trace-schema.md), [`docs/T3-trace.md`](../../T3-trace.md)
- Rulebook + checker harness: [`docs/tf-check/USAGE.md`](../../tf-check/USAGE.md)

> **Troubleshooting**
>
> - `tf run.mjs: no capabilities provided` – the pilot helper injects caps automatically. If you run `run.mjs` manually, pass `--caps tests/fixtures/caps-pilot.json`.
> - `node scripts/validate-trace.mjs …` exits non-zero – confirm you passed the hashes from the fresh `status.json`; stale IR/catalog hashes cause schema mismatches.
> - Permission denied under `out/0.5/pilot-l0` – remove or `chmod` existing directories created by another user before re-running the helper.
