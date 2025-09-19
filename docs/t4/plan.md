# T4 Plan Explorer

The T4 Plan Explorer enumerates design branches from a Terraform spec, scores them with deterministic heuristics, and provides tooling to scaffold comparison workstreams. All command outputs are validated against the shared JSON Schemas exported by `@tf-lang/tf-plan-core`, ensuring the same checks run in the CLI and in CI.

## Deterministic workflow

Every CLI accepts a `--seed` flag (defaulting to `42`) so repeated runs produce identical hashes and ordering. The generated `plan.json`, `plan.ndjson`, scaffold index, and compare artifacts embed `{ seed, specHash }` metadata blocks so downstream tooling can verify provenance.

```bash
pnpm -r build

# Enumerate the plan with schema validation and deterministic seeds
pnpm exec tf-plan enumerate \
  --spec tests/specs/demo.json \
  --seed 42 \
  --beam 3 \
  --out out/t4/plan

# Scaffold the top branches (will reuse the seed from plan.json unless overridden)
pnpm exec tf-plan-scaffold scaffold \
  --plan out/t4/plan/plan.ndjson \
  --graph out/t4/plan/plan.json \
  --seed 42 \
  --top 3 \
  --template dual-stack \
  --out out/t4/scaffold/index.json

# Compare the scaffolded branches against the plan nodes with a deterministic render
pnpm exec tf-plan-compare compare \
  --plan out/t4/plan/plan.ndjson \
  --inputs out/t4/scaffold/index.json \
  --seed 42 \
  --out out/t4/compare
```

### Validation & hygiene

* `tf-plan enumerate` hashes the spec, validates the resulting plan graph and branch nodes, and writes canonical JSON/NDJSON.
* `tf-plan-scaffold scaffold` revalidates the input plan (or NDJSON fallback) before creating the scaffold summary.
* `tf-plan-compare compare` validates both the input nodes and the generated compare report before emitting Markdown, JSON, and HTML reports.

## Adding scoring plugins

Extend `@tf-lang/tf-plan-scoring` with new dimension helpers and wire them into `scorePlanNode`. Each helper should return both a numeric score and a textual explanation to maintain deterministic rationales. Update tests to assert deterministic totals and regenerate any golden fixtures.
