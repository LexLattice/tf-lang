# T4 Plan Explorer

The T4 Plan Explorer enumerates design branches from a Terraform spec, scores them with deterministic heuristics, and provides tooling to scaffold comparison workstreams.

## Quick start

```bash
pnpm -r build
pnpm exec tf-plan enumerate --spec tests/specs/demo.json --seed 42 --beam 3 --max 5 --out out/t4/plan
pnpm exec tf-plan-scaffold scaffold --plan out/t4/plan/plan.ndjson --graph out/t4/plan/plan.json --top 3 --template dual-stack --seed 42 --out out/t4/scaffold/index.json
pnpm exec tf-plan-compare compare --plan out/t4/plan/plan.ndjson --inputs out/t4/scaffold/index.json --seed 42 --out out/t4/compare
```

Every command validates its JSON inputs and outputs against the shared schemas from `@tf-lang/tf-plan-core`. Failures surface as readable errors before any files are written.

## Deterministic artifacts & seeds

* All CLIs accept `--seed` (default `42`) and persist the chosen seed alongside the `specHash` inside each artifact’s `meta` block.
* Re-running `tf-plan enumerate` with the same seed yields identical `plan.json` and `plan.ndjson` byte-for-byte; tests enforce the hashes.
* Scaffolds inherit the `specHash` from the plan JSON (or from the supplied seed when only NDJSON is available) so downstream compare runs remain reproducible.

## Security & validation

* Schema validation is centralized in `@tf-lang/tf-plan-core` with Ajv strict mode enabled; CLI helpers call `validatePlan`, `validateBranch`, and `validateCompare` before writing artifacts.
* Compare HTML rendering escapes all dynamic content, applies a restrictive Content Security Policy, and avoids external scripts/styles. See [docs/t4/compare.md](./compare.md) for details.

## Extending scoring plugins

Extend `@tf-lang/tf-plan-scoring` with new dimension helpers and wire them into `scorePlanNode`. Each helper should return both a numeric score and a textual explanation to maintain deterministic rationales. Update tests to assert deterministic totals and regenerate any golden fixtures.
