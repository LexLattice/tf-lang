# TF‑Lang (v0.6) — True Functions, Algebra & Deterministic Pipelines

[![Pages](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml/badge.svg?branch=main)](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml)

**Live site:** [https://LexLattice.github.io/tf-lang/](https://LexLattice.github.io/tf-lang/)

## TF-Lang v0.6 — What’s new

- Minimal **L0 kernel** (Transform, Publish, Subscribe, Keypair) with effect derivation and human-readable `tf check --summary`.
- **Macro growth** across state/process/policy/time/auth, including deterministic YAML parsing for multi-line macros.
- **Runtime tooling**: `tf runtime exec --trace`, adapter skeleton emission, and expanded law diagnostics.
- **Instance planning**: registry v2, table rendering, and per-node explanations via `tf plan --format table --explain`.
- **Docs & onboarding**: consolidated quickstarts, contributor guide, and annotated example scenarios.

Entry points: [v0.6 review](out/0.6/review/README.md), [Top issues roll-up](out/0.6/review/_summary/ALL.md), [Track proposals](out/0.6/review/_proposals/INDEX.md), [Examples index](examples/v0.6/).

---

## Quickstart

### Requirements

- Node.js 18+
- pnpm 8+

Verify your toolchain and install workspace dependencies:

```bash
pnpm -v && node -v
pnpm -w install --frozen-lockfile
```

### Explore the fast-track pipeline

```bash
# Discover available subcommands
pnpm tf --help

# Expand the L2 pipeline into its canonical L0 DAG
pnpm tf expand examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml --out out/0.6/tmp/fnol.l0.json

# Summarize effects, policy coverage, capabilities, and law status
pnpm tf check out/0.6/tmp/fnol.l0.json --summary

# Plan runtime instances and see which registry rule fired
pnpm tf plan out/0.6/tmp/fnol.l0.json --format table --explain

# Inspect the runtime trace with determinism markers
pnpm tf runtime exec out/0.6/tmp/fnol.l0.json --trace
```

### Run focused checks

```bash
# Type inference with adapter suggestions
pnpm tf typecheck out/0.6/tmp/fnol.l0.json

# Emit adapter scaffolding for mismatched ports
pnpm tf typecheck out/0.6/tmp/fnol.l0.json --emit-adapters out/0.6/tmp/adapters

# Execute the example suite
bash tasks/run-examples.sh
```

Additional track-specific recipes live under [`docs/`](docs/) and are linked from the [v0.6 documentation index](docs/0.6/index.md).

---

## Documentation map

- [TF-Lang v0.6 index](docs/0.6/index.md) — pipelines, monitors, and CLI entry points.
- [Instance planning guide](docs/0.6/instance-planning.md) — registry precedence, hints, and explain mode.
- [Port type metadata reference](docs/0.6/port-types.md) — wildcards, defaults, and validator behavior.
- [Authoring new laws](docs/0.6/laws-authoring.md) — goal scaffolds, SMT capture, and evidence layout.
- [Examples catalog](examples/v0.6/README.md) — scenario walkthroughs and troubleshooting tips.
- [Contributor guide](CONTRIBUTING.md) — repository setup, workflows, and testing expectations.

---

## Continuous integration

[CI: T4 Plan/Scaffold/Compare](.github/workflows/t4-plan-scaffold-compare.yml) •
[CI: T3 Trace & Perf](.github/workflows/t3-trace-and-perf.yml) •
[CI: L0 Runtime Verify](.github/workflows/l0-runtime-verify.yml) •
[CI: L0 Docs (Sync)](.github/workflows/l0-docs.yml) •
[CI: L0 Proofs (Emit)](.github/workflows/l0-proofs.yml) •
[CI: L0 Audit](.github/workflows/l0-audit.yml)

Version: **v0.6**

Historical quickstarts for earlier releases remain available in [`docs/0.5/`](docs/0.5/).

---

## Project layout

- `examples/v0.6/` — runnable L2 pipelines with golden L0 builds and contract tests.
- `packages/` — expander, runtime, typechecker, prover, and supporting libraries.
- `tools/tf-lang-cli/` — CLI entry point providing `tf`, `tf plan`, `tf check`, and friends.
- `policy/` and `laws/` — effect lattice, capability policies, and prover goals.
- `out/` — generated artifacts (reports, SMT instances, review docs).

See [CONTRIBUTING.md](CONTRIBUTING.md) for coding standards, docs workflows, and verification steps before opening a pull request.

---

## License

[Apache License 2.0](LICENSE)
