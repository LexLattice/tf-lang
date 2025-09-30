# Track A — Parse & Format Quickstart

Stay on the CLI surface that feeds every other track: regenerate IDs/catalog, parse DSL flows, and confirm canonical formatting.

## Prerequisites

- `pnpm -w -r install --frozen-lockfile`
- Example flow: `examples/flows/signing.tf`
- `jq` available on your `PATH`

## Commands (3–7 steps)

```bash
FLOW=examples/flows/signing.tf
OUT=out/0.5/a-track
pnpm run a1
pnpm run tf -- parse "$FLOW" -o "$OUT/signing.ir.json"
pnpm run tf -- canon "$FLOW" -o "$OUT/signing.canon.json"
pnpm run tf -- fmt "$FLOW" | tee "$OUT/signing.fmt.tf"
jq -c '.children[0]' "$OUT/signing.ir.json"
```

## Expected output

```
> tf-lang@0.0.2 a1 /workspace/tf-lang
catalog.json written with 14 primitives (seed union applied).
...
{"args":{},"node":"Prim","prim":"serialize","raw":"serialize"}
serialize |> hash |> authorize{
  sign-data(key_ref="k1")
}
```

*Artifacts land under `out/0.5/a-track/**`. The parse/canon IRs are newline-terminated JSON; the formatter mirrors [`docs/l0-dsl.md`](../../l0-dsl.md) spacing rules.*

## Where next?

- DSL tokens & grammar: [`docs/l0-dsl.md`](../../l0-dsl.md)
- Catalog + effects derivation: [`docs/l0-catalog.md`](../../l0-catalog.md), [`docs/l0-effects.md`](../../l0-effects.md)
- Checker & rulebook CLI: [`docs/tf-check/USAGE.md`](../../tf-check/USAGE.md)

> **Troubleshooting**
>
> - `node: command not found` – ensure you are on Node 20+ (check with `node -v`).
> - pnpm warnings about lock drift – rerun `pnpm -w install --lockfile-only`, then repeat the quickstart.
> - `jq: command not found` – install `jq` or drop the final verification line; all earlier steps still succeed.
