# TF-Lang v0.6 Examples

This directory collects runnable L2 pipelines that expand into L0 DAGs. Each scenario is paired with golden outputs under `build/`, a registry snapshot, and targeted contract tests.

## Scenario overview

| Pipeline | Description | Key commands |
| --- | --- | --- |
| `auto.fnol.fasttrack.v1.l2.yaml` | Fast-track first notice of loss (FNOL) workflow with policy + auth macros and SLA monitors. | `pnpm tf expand examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml --out out/0.6/tmp/fnol.l0.json` |
| `auto.quote.bind.issue.v2.l2.yaml` | Quote → Bind → Issue lifecycle showcasing state merges, notifications, and law coverage. | `pnpm tf expand examples/v0.6/pipelines/auto.quote.bind.issue.v2.l2.yaml --out out/0.6/tmp/quote.l0.json` |

After expansion you can reuse the CLI across both builds:

```bash
pnpm tf check <out_file>.json --summary
pnpm tf plan <out_file>.json --format table --explain
pnpm tf runtime exec <out_file>.json --trace
pnpm tf typecheck <out_file>.json
```

## Instance planning registry

`registry/fasttrack.instances.json` provides a concrete planning catalog for the fast-track scenario. Override hints with `--registry` to test alternative deployments:

```bash
pnpm tf plan out/0.6/tmp/fnol.l0.json --registry examples/v0.6/registry/fasttrack.instances.json --format table --explain
```

The [instance planning guide](../../docs/0.6/instance-planning.md) explains precedence between pipeline hints, registry defaults, and CLI overrides.

## Running the suite

```bash
bash tasks/run-examples.sh
```

The script rebuilds each pipeline, runs the contract tests under `examples/v0.6/tests`, and regenerates DOT diagrams in the `diagrams/` directory when Graphviz is installed.

## Parser rules & authoring tips

- Pipelines are authored as plain YAML with macro invocations written as bare function-style calls (`interaction.receive(...)`).
- The expander relies on an AST loader that preserves the original text of macro calls, so inline comments after a macro (`# foo`) and arguments that span multiple lines are supported without additional quoting.
- Macro invocations must include balanced parentheses; the loader raises a descriptive error if a closing `)` is missing.
- Standard YAML constructs remain available for everything else (block scalars, flow maps/arrays, etc.). Values inside macro arguments are parsed using normal YAML rules, so nested objects, lists, and string interpolation still work as before.

## Troubleshooting

- **Missing Graphviz:** diagram regeneration is optional; install `graphviz` (`brew install graphviz` or `apt-get install graphviz`) if you want `.dot` and `.svg` outputs.
- **Stale builds:** rerun `pnpm tf expand ... --out examples/v0.6/build/<file>.json` to refresh golden L0 artifacts when macros change.
- **YAML parse errors:** ensure macro arguments keep consistent indentation and avoid stray `#` characters inside unquoted strings. Use block scalars (`|`) for multi-line payloads when in doubt.

For more context on macro signatures and law coverage, read the [TF-Lang v0.6 documentation index](../../docs/0.6/index.md).
