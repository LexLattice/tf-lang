# @tf-lang/tf-check

`tf-check` is a deterministic CLI for validating TF-Lang specs. It parses a spec, reports canonical summaries, and emits CI-friendly artifacts under `out/t2/tf-check/`.

## Commands

```bash
# show help
pnpm --filter @tf-lang/tf-check run build && node dist/cli.js --help

# validate a spec
pnpm --filter @tf-lang/tf-check run build
node dist/cli.js validate --input fixtures/sample-spec.json

# emit artifacts (help.txt + result.json)
pnpm --filter @tf-lang/tf-check run build
pnpm --filter @tf-lang/tf-check run artifacts
```

All outputs are canonical JSON with sorted keys. Determinism is enforced by rerunning validations twice in CI.
