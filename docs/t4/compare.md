# T4 Compare Renderer

The compare stage consumes enumerated plans and scaffold indices to produce a schema-validated report alongside Markdown and HTML renderings.

## Running locally

```bash
pnpm -r build
pnpm exec tf-plan enumerate --spec tests/specs/demo.json --seed 42 --beam 3 --out out/t4/plan
pnpm exec tf-plan-scaffold scaffold --plan out/t4/plan/plan.ndjson --graph out/t4/plan/plan.json --top 3 --template dual-stack --out out/t4/scaffold/index.json --seed 42
pnpm exec tf-plan-compare compare --plan out/t4/plan/plan.ndjson --inputs out/t4/scaffold/index.json --out out/t4/compare --seed 42
```

Each command validates its inputs against the shared schemas published by `@tf-lang/tf-plan-core` and writes canonical JSON with a trailing newline for deterministic diffs.

## Security

The HTML renderer escapes every dynamic field (branch names, summaries, oracle metadata, notes) and renders them as plain text. Links are emitted as text rather than `<a>` tags, and a restrictive Content-Security-Policy disables scripts, external resources, and inline event handlers. Inputs containing HTML are preserved as text (e.g. `&lt;script&gt;alert(1)&lt;/script&gt;`), so no raw HTML from plan data reaches the browser.

## Deterministic artefacts

`report.json`, `report.md`, and `index.html` are deterministic for a given `{ seed, specHash }`. Re-running the pipeline with the same seed yields identical content, which is enforced in tests and relied upon by CI artefact comparisons.
