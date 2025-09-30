# Track D — Optimizer Quickstart

Run the rewrite detector on a canonical plan and capture the law manifest for downstream proofs.

## Prerequisites

- Track A canonical IR available (or re-run `pnpm run tf -- canon`)
- `out/0.5/proofs/` writeable for manifests
- `node` (20+) and `jq`

## Commands (3–7 steps)

```bash
FLOW=examples/flows/signing.tf
OUT=out/0.5/optimizer
mkdir -p "$OUT"
pnpm run tf -- canon "$FLOW" -o "$OUT/signing.canon.json"
node packages/tf-opt/bin/opt.mjs --ir "$OUT/signing.canon.json" --out "$OUT/signing.optimized.json"
node packages/tf-opt/bin/opt.mjs --ir "$OUT/signing.canon.json" --emit-used-laws out/0.5/proofs/signing.used-laws.json
node scripts/proofs/coverage.mjs --out out
```

## Expected output

```
{"rewrites_applied":0,"used_laws":[]}
{"ok": true, "missing": [], "covered": []}
```

*Optimizer outputs include both the rewritten plan and `used_laws` manifest. The coverage script cross-checks manifests against committed stubs under `scripts/proofs/laws/`.*

## Where next?

- Optimizer internals & rewrite detection: [`packages/tf-opt/`](../../../packages/tf-opt/)
- Law manifest validation gate: [`docs/proofs/README.md#manifest-validation-ci-gatemjs---check-used`](../../proofs/README.md#manifest-validation-ci-gatemjs---check-used)
- Adding SMT law stubs: [`docs/proofs/README.md#law-stubs-scriptsproofslaws`](../../proofs/README.md#law-stubs-scriptsproofslaws)

> **Troubleshooting**
>
> - `Cannot find module tf-opt` – ensure `pnpm -w -r build` completed; the optimizer uses generated entry points.
> - Coverage reports missing laws – add the stub under `scripts/proofs/laws/` before rerunning `node scripts/proofs/coverage.mjs --out out`.
> - Writing to `out/0.5/proofs` fails – create the directory with `mkdir -p out/0.5/proofs` and check permissions.
