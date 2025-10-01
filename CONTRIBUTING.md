# Contributing to TF-Lang

Thanks for helping extend TF-Lang! This guide walks through local setup, day-to-day workflows, and the reference material you need to keep pipelines deterministic and auditable.

## Prerequisites

- Node.js 18 or newer
- pnpm 8 or newer (`corepack enable pnpm` installs it alongside Node.js)
- Optional: Graphviz (`dot`) to regenerate diagrams in `diagrams/`

Verify your environment:

```bash
pnpm -v && node -v
```

## Repository setup

```bash
git clone https://github.com/LexLattice/tf-lang.git
cd tf-lang
pnpm -w install --frozen-lockfile
```

The workspace exposes the CLI directly, so `pnpm tf <command>` resolves to `tools/tf-lang-cli/index.mjs`.

## Common workflows

### Expand, check, and summarize a pipeline

```bash
pnpm tf expand examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml --out out/0.6/tmp/fnol.l0.json
pnpm tf check out/0.6/tmp/fnol.l0.json --summary
```

### Plan runtime instances

```bash
pnpm tf plan out/0.6/tmp/fnol.l0.json --format table --explain
```

Provide `--registry <path>` to simulate different deployment targets and review how hints influence the resolution order. See [docs/0.6/instance-planning.md](docs/0.6/instance-planning.md) for precedence rules.

### Type inference & adapters

```bash
pnpm tf typecheck out/0.6/tmp/fnol.l0.json
pnpm tf typecheck out/0.6/tmp/fnol.l0.json --emit-adapters out/0.6/tmp/adapters
```

Adapter suggestions follow the descriptors declared under `metadata.port_types`. The new [port type reference](docs/0.6/port-types.md) explains wildcards, defaults, and validation behavior.

### Runtime traces & law diagnostics

```bash
pnpm tf runtime exec out/0.6/tmp/fnol.l0.json --trace
pnpm tf laws --check out/0.6/tmp/fnol.l0.json --goal branch-exclusive --verbose
```

Trace entries are annotated with deterministic vs. non-deterministic transforms. Verbose law checks surface SMT-LIB paths and solver flags; evidence is written under `out/laws/<pipelineId>/`.

### Examples & regression tests

```bash
bash tasks/run-examples.sh
node --test tools/tf-lang-cli/tests/plan.instances.test.mjs
```

Each sub-package includes dedicated tests. Use `node --test <file>` for focused runs or `pnpm run test:fast` to execute the standard suite.

## Documentation sources

- Macro catalog & pipeline walkthroughs live under [`docs/0.6/`](docs/0.6/).
- Law authoring guidance is collected in [docs/0.6/laws-authoring.md](docs/0.6/laws-authoring.md).
- Example-specific troubleshooting tips live in [examples/v0.6/README.md](examples/v0.6/README.md).

Please update the relevant references whenever you change macro signatures, law behaviors, or CLI surfaces.

## Pull request checklist

- [ ] Regenerate artifacts deterministically (no manual edits to L0 JSON).
- [ ] Run the targeted tests and record results in the PR description.
- [ ] Keep documentation in sync, especially CLI usage examples and law references.
- [ ] Include citations for new laws, macros, or instance planning rules in the review docs when applicable.

Following these steps ensures TF-Lang continues to provide an explainable, reproducible path from human-readable pipelines to immutable L0 formulas.
