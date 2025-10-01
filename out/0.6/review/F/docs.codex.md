# Track F · Types & capabilities

## What exists now
- **Typechecker** (`packages/typechecker/typecheck.mjs`): infers port bindings, reports mismatches, suggests adapters; `tf typecheck` wraps it with registry overrides.
- **Adapter registry** (`adapters/registry.json`): three sample adapters (CSV↔JSON, FNOL CSV→JSON) demonstrating schemaRef/format descriptors.
- **Capability lattice** (`policy/capability.lattice.json`): maps publish/subscribe patterns and keypair algorithms to capability IDs used by the checker.
- **Policy allowlist** (`policy/policy.allow.json`): default publish/subscribe/keypair allowances feeding both policy + capability checks.

## How to run
```bash
# Basic typecheck (uses adapters/registry.json by default)
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.quote.bind.issue.v2.l0.json

# Inspect adapter suggestions
node tools/tf-lang-cli/index.mjs typecheck <L0_WITH_MISMATCHES> --adapters adapters/registry.json

# Capability diff inside checker report
node packages/checker/check.mjs <L0> --policy policy/policy.allow.json --caps policy/policy.allow.json --out out/report.json
```

## Common errors + fixes
- `FAILED with N mismatch(es)` → add missing adapter entry in `adapters/registry.json` or correct schemaRef in the pipeline. Re-run to confirm `OK` or `OK with suggestions`.
- Passing `--caps` a lattice file causes checker to flag all capabilities missing; always point to an allowlist JSON listing granted caps (wildcards allowed).
- Adapter registry load errors (ENOENT) degrade silently to zero adapters; the CLI still exits 0. Document this so teams know to check logs if suggestions disappear.

## Gaps
- No documentation of schemaRef catalogue (what does `AutoQuoteOfferV2` mean?); authors must guess.
- `tf typecheck` lacks `--json` output, making CI parsing hard.
- No canned adapter scaffolding script; adding adapters is manual JSON editing.

## Next 3 improvements
1. Generate a `docs/0.6/types/index.md` enumerating available schemaRefs + example payloads pulled from catalogs/tests.
2. Extend `tf typecheck` with `--json` to emit machine-readable mismatch/suggestion output for automation.
3. Add `tf adapters scaffold --from schema --to schema` helper that appends registry entries with descriptive stubs.
