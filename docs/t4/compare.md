# T4 Compare Reports

The compare stage ranks scaffolded branches against an enumerated plan and emits JSON, Markdown, and HTML reports. All inputs and outputs are validated against the shared schemas from `@tf-lang/tf-plan-core` and the renderer escapes **every** dynamic field to prevent XSS.

## Running locally

```bash
pnpm -r build

pnpm exec tf-plan enumerate \
  --spec tests/specs/demo.json \
  --seed 42 \
  --out out/t4/plan

pnpm exec tf-plan-scaffold scaffold \
  --plan out/t4/plan/plan.ndjson \
  --graph out/t4/plan/plan.json \
  --seed 42 \
  --top 3 \
  --template dual-stack \
  --out out/t4/scaffold/index.json

pnpm exec tf-plan-compare compare \
  --plan out/t4/plan/plan.ndjson \
  --inputs out/t4/scaffold/index.json \
  --seed 42 \
  --out out/t4/compare
```

Each run produces:

* `out/t4/compare/report.json` (schema-validated and canonical)
* `out/t4/compare/report.md` (Markdown summary for PRs)
* `out/t4/compare/index.html` (fully escaped static HTML with a locked-down CSP)

The renderer will reject invalid JSON and the HTML output never embeds raw user content—plan names, rationales, metrics, and oracle details are HTML-escaped, and potentially dangerous links (`javascript:` schemes, etc.) are dropped.
