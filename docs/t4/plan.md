# T4.1 — tf-plan branch enumeration

The `tf-plan` tool enumerates viable design branches from a `tf-spec` design space, applies deterministic scoring, and prepares artifacts consumed by the scaffolder and comparison workflows.

## Packages

* `@tf-lang/tf-plan-core` — canonical types, helpers, and JSON schema validation for plan graphs.
* `@tf-lang/tf-plan-scoring` — deterministic scoring plugins for component choices and aggregate branches.
* `@tf-lang/tf-plan-enum` — design space enumerator with constraint pruning and beam search.
* `@tf-lang/tf-plan` — CLI entry point and thin orchestration helpers.

## CLI usage

```bash
pnpm --filter @tf-lang/tf-plan run build
node packages/tf-plan/dist/cli.js enumerate \
  --spec tests/specs/demo.json \
  --seed 42 \
  --beam 6 \
  --out out/t4/plan

node packages/tf-plan/dist/cli.js export \
  --plan out/t4/plan/plan.json \
  --ndjson out/t4/plan/plan.ndjson \
  --plans-only
```

The enumerate command writes a canonical `plan.json` file and prints a ranked summary. The export command emits stable NDJSON (one node per line) for downstream automation.

## Adding scoring signals

`@tf-lang/tf-plan-scoring` exposes plugin-style helpers. To adjust scoring for a new signal:

1. Extend the `RepoSignals` interface with the new dimension.
2. Update the relevant plugin in `src/plugins.ts` to incorporate the signal deterministically.
3. Add a Vitest covering the new behaviour in `packages/tf-plan-scoring/tests`.

Scores remain deterministic because all randomness flows through `createSeededRng` and seed-aware node IDs.

## Artifacts

Running the CLI produces:

* `out/t4/plan/plan.json` — full plan graph, validated against `schema/tf-plan.schema.json`.
* `out/t4/plan/plan.ndjson` — NDJSON stream for consumption by the scaffolder.

Downstream stages reuse the same schemas (`schema/tf-branch.schema.json`, `schema/tf-compare.schema.json`) for consistent contract enforcement.
