# T4 Plan Explorer

The T4 Plan Explorer enumerates design branches from a Terraform spec, scores them with deterministic heuristics, and provides tooling to scaffold comparison workstreams.

## Quick start

```bash
pnpm -r build
pnpm exec tf-plan enumerate --spec tests/specs/demo.json --seed 42 --beam 3 --out out/t4/plan
pnpm exec tf-plan-scaffold scaffold --plan out/t4/plan/plan.ndjson --graph out/t4/plan/plan.json --top 3 --template dual-stack --out out/t4/scaffold/index.json --seed 42
pnpm exec tf-plan-compare compare --plan out/t4/plan/plan.ndjson --inputs out/t4/scaffold/index.json --out out/t4/compare --seed 42
```

All CLIs validate their inputs against the shared JSON Schemas in `@tf-lang/tf-plan-core` and fail fast when artefacts are malformed. The `meta` block emitted by each command includes `{ seed, specHash }`, ensuring runs are reproducible when the same seed is supplied.

## Deterministic pipelines

Running `tf-plan enumerate` multiple times with the same `--seed` produces byte-for-byte identical `plan.json` and `plan.ndjson` artefacts. Scaffold and compare reuse the same seed so that reports and dry-runs can be diffed confidently in CI.

See [docs/t4/compare.md](./compare.md) for details on rendering and security guarantees.

## Adding scoring plugins

Extend `@tf-lang/tf-plan-scoring` with new dimension helpers and wire them into `scorePlanNode`. Each helper should return both a numeric score and a textual explanation to maintain deterministic rationales. Update tests to assert deterministic totals and regenerate any golden fixtures.
