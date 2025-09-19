# T4 Plan Explorer

The T4 Plan Explorer enumerates design branches from a Terraform spec, scores them with deterministic heuristics, and provides tooling to scaffold comparison workstreams.

## Quick start

```bash
pnpm -r build
pnpm exec tf-plan enumerate --spec tests/specs/demo.json --seed 42 --beam 3 --out out/t4/plan
pnpm exec tf-plan-scaffold scaffold --plan out/t4/plan/plan.ndjson --graph out/t4/plan/plan.json --top 3 --template dual-stack --out out/t4/scaffold/index.json
pnpm exec tf-plan-compare compare --plan out/t4/plan/plan.ndjson --inputs out/t4/scaffold/index.json --out out/t4/compare
```

## Adding scoring plugins

Extend `@tf-lang/tf-plan-scoring` with new dimension helpers and wire them into `scorePlanNode`. Each helper should return both a numeric score and a textual explanation to maintain deterministic rationales. Update tests to assert deterministic totals and regenerate any golden fixtures.
