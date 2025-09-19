# T4 Compare Reports

`tf-plan-compare` consumes the ranked plan artifacts and scaffold indices produced by the enumerate/scaffold stages. The CLI validates every JSON input against the shared schemas from `@tf-lang/tf-plan-core`, then emits a deterministic report trio (`report.json`, `report.md`, `index.html`).

## Running locally

```bash
pnpm -r build
pnpm exec tf-plan enumerate --spec tests/specs/demo.json --seed 42 --out out/t4/plan
pnpm exec tf-plan-scaffold scaffold --plan out/t4/plan/plan.ndjson --graph out/t4/plan/plan.json --top 3 --template dual-stack --seed 42 --out out/t4/scaffold/index.json
pnpm exec tf-plan-compare compare --plan out/t4/plan/plan.ndjson --inputs out/t4/scaffold/index.json --seed 42 --out out/t4/compare
```

The `--seed` flag (default `42`) is persisted in the compare report metadata along with the originating `specHash` and plan version. Re-running the command with the same seed regenerates byte-identical markdown and HTML.

## Renderer security

* Input reports are validated against `tf-compare.schema.json` before rendering. Invalid data aborts the run with a clear message.
* All dynamic fields are HTML-escaped (branch names, rationales, oracle notes, artifacts). Links are rendered as plain text, eliminating injection vectors.
* The generated HTML sets a restrictive `Content-Security-Policy` (`default-src 'none'`) and bundles minimal inline CSS—no external scripts or styles are allowed.

Use the Markdown report (`report.md`) for quick text diffs and the HTML report (`index.html`) for a structured view that is safe to open in any modern browser.
