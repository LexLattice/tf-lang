# @tf-lang/coverage-generator

Consumes tag streams from `@tf-lang/trace2tags` and emits deterministic coverage summaries plus a static HTML report.

## Outputs

- `coverage.json` — canonical JSON summary (sorted keys, newline terminated)
- `coverage.html` — static table for quick inspection

## Usage

```bash
pnpm --filter @tf-lang/coverage-generator run build
pnpm --filter @tf-lang/coverage-generator run artifacts
```

By default the generator reads `out/t2/trace-tags.json` and writes results into `out/t2/`.
