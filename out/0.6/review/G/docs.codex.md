# Track G · Instance hints & planning

## What exists now
- **Registry v2** (`instances/registry.v2.json`): rule-based selection by domain/QoS/channel with defaults per domain and global fallback.
- **Resolver** (`packages/expander/resolve.mjs`): loads registry.v2 (fallback to registry.json), normalizes channels/QoS, annotates nodes with `runtime.domain` + `runtime.instance`.
- **Planner CLI** (`tf plan-instances`): summarizes counts per domain and per channel scheme, supports `--registry` override and `--group-by domain|scheme`.
- **Tests**: cover fallback when registry.v2 missing, QoS arrays, and explicit overrides.

## How to run
```bash
# Default plan from shipped L0
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.quote.bind.issue.v2.l0.json

# Group by channel scheme
node tools/tf-lang-cli/index.mjs plan-instances --group-by scheme examples/v0.6/build/auto.quote.bind.issue.v2.l0.json

# Use custom registry
node tools/tf-lang-cli/index.mjs plan-instances --registry my/registry.json <L0>
```

## Common errors + fixes
- Missing registry file → planner falls back to `@Memory` silently. Pass `--registry` explicitly in docs/tests to avoid confusion.
- `--group-by` typo yields `unknown option`; CLI emits usage text but exit code 2 — highlight valid values in docs.
- Dynamic channels (e.g., `@reply_to_*`) collapse under `dynamic`; provide context when presenting totals so infra teams know these require runtime wiring.

## Gaps
- No documentation for registry schema (fields, wildcards, precedence) beyond code comments.
- Planner output is JSON only; no table/markdown summarizer for release notes.
- Annotated instances are not persisted back into L0 or diagrams, so reviewers cannot see placement decisions without rerunning CLI.

## Next 3 improvements
1. Publish `docs/0.6/instances.md` explaining registry format, precedence rules, and sample overrides per domain.
2. Add `--out table`/`--out markdown` support to `tf plan-instances` for copy-pasting into reviews.
3. Embed planner results when emitting L0 (e.g., store under `l0.runtime.instances`) so downstream tooling can skip recomputation.
