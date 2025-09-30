# Track C — Trace & Perf Quickstart

Summarize trace traffic, validate provenance hashes, and prep for parity drills.

## Prerequisites

- Completed Track B run (`out/0.5/pilot-l0/**` populated)
- `jq` installed
- Access to `tests/fixtures/trace-sample.jsonl`

## Commands (3–7 steps)

```bash
OUT=out/0.5/trace
mkdir -p "$OUT"
pnpm run traces:sample > "$OUT/sample-summary.json"
jq '.total' "$OUT/sample-summary.json"
pnpm run traces:validate --require-meta \
  --ir "$(jq -r .provenance.ir_hash out/0.5/pilot-l0/status.json)" \
  --manifest "$(jq -r .provenance.manifest_hash out/0.5/pilot-l0/status.json)" \
  --catalog "$(jq -r .provenance.catalog_hash out/0.5/pilot-l0/status.json)" \
  < out/0.5/pilot-l0/trace.jsonl
head -n 5 "$OUT/sample-summary.json"
```

## Expected output

```
10
{"invalid":0,"meta_checked":true,"ok":true,"total":5}
{
  "by_effect": {
    "Network.Out": 3,
    "Observability": 2,
    "Pure": 3,
    "Storage.Write": 2
  },
  ...
}
```

*Summaries stay deterministic because `trace-summary.mjs` emits sorted keys with a trailing newline. Use them to diff perf regressions or feed dashboards.*

## Where next?

- Trace schema & meta fields: [`docs/trace-schema.md`](../../trace-schema.md)
- Parity harness and expected artifacts: [`docs/pilot-l0.md#parity-harness`](../../pilot-l0.md#parity-harness)
- Perf drill-down tooling: [`docs/T3-trace.md`](../../T3-trace.md)

> **Troubleshooting**
>
> - `pnpm run traces:sample` emits EPIPE – avoid piping through `head`; redirect to a file first as shown above.
> - Trace validation fails on catalog hash – ensure Track A regenerated the catalog and rerun Track B before re-validating.
> - `pnpm run pilot:parity` fails with missing `manual/status.json` – run `pnpm run pilot:manual` to refresh the handwritten baseline before diffing parity.
