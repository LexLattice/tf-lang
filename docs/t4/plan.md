# T4.1 — Plan Enumeration

The `@tf-lang/tf-plan` toolset turns a [tf-spec](../../schema/tf-spec.schema.json) into a reproducible plan graph. The core libraries live in dedicated packages so the enumerator and CLI can be reused across T4 automation:

- `@tf-lang/tf-plan-core` — shared types, scoring container, and deterministic helpers.
- `@tf-lang/tf-plan-scoring` — pure heuristics for complexity, risk, performance, development effort, and dependency readiness.
- `@tf-lang/tf-plan-enum` — graph generator that explores the branch space and emits a stable plan graph.
- `@tf-lang/tf-plan` — CLI wrapper that exposes enumeration, scoring, and export commands.

## Quick start

```bash
pnpm --filter @tf-lang/tf-plan build
node packages/tf-plan/dist/cli.js enumerate --spec tests/specs/demo.json --seed 42 --beam 5 --out out/t4/plan
```

Outputs land under `out/t4/plan` and are validated against `schema/tf-plan.schema.json` before being written. The CLI also writes an NDJSON view:

```
out/t4/plan/plan.json
out/t4/plan/plan.ndjson
```

To re-score an existing plan (for example after adjusting the heuristics):

```bash
node packages/tf-plan/dist/cli.js score --plan out/t4/plan/plan.json --out out/t4/plan/plan.scored.json
```

And to export only the NDJSON projection:

```bash
node packages/tf-plan/dist/cli.js export --plan out/t4/plan/plan.json --ndjson out/t4/plan/plan.ndjson
```

All commands accept `--seed` (default 42) and guarantee deterministic IDs, ordering, and totals.

## Adding scoring plugins

1. Implement the new metric in `packages/tf-plan-scoring/src/index.ts`. Functions must be pure and accept `(component, choice, repoSignals?)`.
2. Update `scorePlanNode` so the metric contributes to the aggregate `createScore` call. Keep the textual `explain` output concise.
3. Extend unit tests in `packages/tf-plan-scoring/tests/` to cover the new behavior.
4. Re-run `pnpm --filter @tf-lang/tf-plan-scoring test` to confirm determinism and coverage.

Because the CLI rescores plans through the shared helpers, any new heuristics automatically flow into exported artifacts.
