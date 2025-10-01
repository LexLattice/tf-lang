# Track A · Platform scaffolding

## What exists now
- **Schemas**: A comprehensive set of JSON schemas under `schemas/` defines core data structures, including `l2-pipeline`, `l0-dag`, `effects`, `manifest`, and `law`. Schemas for older versions (v0.4) are present alongside current ones.
- **CLI**: The primary CLI entry point is `tools/tf-lang-cli/index.mjs`. It exposes commands for validation, effects analysis, graph generation, type checking, instance planning, and law verification. Help is available via the `--help` flag.
- **Documentation**: High-level guidance is in `AGENTS.md`. The root `README.md` is for v0.5. A v0.6-specific doc (`docs/0.6/index.md`) exists but notes that detailed specification pages are missing.
- **CI**: GitHub Actions workflows are defined for key quality gates, including runtime verification, proofs, audits, and doc synchronization, as linked in the `README.md`.
- **CLI surface**: `tf` entrypoint (`tools/tf-lang-cli/index.mjs`) covers schema validation, effect summaries, DOT graphing, typecheck, instance planning, and law checks with a single usage banner.
- **Schema set**: `schemas/` includes L0 DAG, L2 pipeline, catalog/effects, manifests, and capability/type scaffolds reused by expander + checker flows.
- **Docs footprint**: v0.5 overview + quickstarts remain; v0.6 landing page lists example pipelines/monitors and macro law notes but auto-generated spec pages are empty.
- **Tasks**: `tasks/run-examples.sh` meant as the 10-min smoke for v0.6 (build → lint → diagrams) invoking CLI helpers + bespoke assertions.

## How to run (10-minute quickstart)
1. **View available commands**.
```bash
node tools/tf-lang-cli/index.mjs --help
```
2. **Validate an L2 pipeline definition**.
```bash
node tools/tf-lang-cli/index.mjs validate l2 examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
```
3. **Validate an L0 build artifact**.
```bash
node tools/tf-lang-cli/index.mjs validate l0 examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
```
4. Ten-minute intended flow: bash tasks/run-examples.sh (expands pipelines + monitors, runs spec scripts, emits diagrams) — currently exits on inline macro comments.
```bash
bash tasks/run-examples.sh
```

## Common errors & fixes
| Symptom | Probable cause | Fix |
| --- | --- | --- |
| `unable to infer schema; pass l0 or l2 explicitly` | Running `validate` without specifying the language level (`l0` or `l2`). | Add the `l0` or `l2` subcommand after `validate`. |
| `tf validate` reports `data/nodes/*/in must be string/null` on v0.6 builds | schema still reflects v0.5 scalar input form. Workaround: skip schema validation or downgrade transforms before release. | skip schema validation or downgrade transforms before release |
| `bash tasks/run-examples.sh` aborts with `invalid call syntax … # types | Because the expander does not strip trailing YAML comments | Because the expander does not strip trailing YAML comments |
| New contributors land in v0.5 docs; no 0.6 quickstart exists yet. Point them at `docs/0.6/index.md` manually and explain missing spec content. | Investigate root cause | Document mitigation |

## Acceptance gates & signals
| Gate | Command | Success signal |
| --- | --- | --- |
| **View available commands** | `node tools/tf-lang-cli/index.mjs --help` | Command succeeds without errors. |
| **Validate an L2 pipeline definition** | `node tools/tf-lang-cli/index.mjs validate l2 examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml` | Command succeeds without errors. |
| **Validate an L0 build artifact** | `node tools/tf-lang-cli/index.mjs validate l0 examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json` | Command succeeds without errors. |
| Ten-minute intended flow: bash tasks/run-examples.sh (expands pipelines + monitors, runs spec scripts, emits diagrams) — currently exits on inline macro comments | `bash tasks/run-examples.sh` | Command succeeds without errors. |

## DX gaps
- **DX Friction (CLI)**: Commands are verbose (`node tools/tf-lang-cli/index.mjs ...`). The `pnpm install` log shows warnings that shorter aliases (e.g., `tf-plan`) failed to be created, indicating a broken or incomplete setup in `package.json`.
- **Documentation (Onboarding)**: The root `README.md` is for v0.5 and does not reflect the v0.6 tools and examples. This creates immediate confusion for new contributors.
- **Documentation (Gaps)**: `docs/0.6/index.md` explicitly states that detailed v0.6 specification pages are missing. There is no central `CONTRIBUTING.md` to guide new developers on workflow, setup, and testing.
- **Schema Versioning**: The presence of v0.4 schemas alongside current schemas in `schemas/` can lead to confusion about which to reference.
- Schema + docs drift from 0.6 kernel shape (structured transform inputs, monitors bundle) blocks validation + onboarding.
- Quickstart script fails out-of-the-box; no happy path to see a green build.
- `docs/0.6/index.md` references empty spec and lacks per-track gate summaries.

## Top issues (synthesized)
- **DX Friction (CLI)**: Commands are verbose (`node tools/tf-lang-cli/index.mjs ...`). The `pnpm install` log shows warnings that shorter aliases (e.g., `tf-plan`) failed to be created, indicating a broken or incomplete setup in `package.json`.
- **Documentation (Onboarding)**: The root `README.md` is for v0.5 and does not reflect the v0.6 tools and examples. This creates immediate confusion for new contributors.
- **Documentation (Gaps)**: `docs/0.6/index.md` explicitly states that detailed v0.6 specification pages are missing. There is no central `CONTRIBUTING.md` to guide new developers on workflow, setup, and testing.

## Next 3 improvements
- **Fix and consolidate CLI aliases** — Action: Correct the `bin` entries in the relevant `package.json` to create simple aliases like `tf`, so commands become `tf validate ...`; Impact: High. Drastically improves CLI ergonomics and discoverability, making local development faster; Effort: Small
- **Update the root `README.md` for v0.6** — Action: Replace v0.5 content with a v0.6-centric quickstart, pointing to `examples/v0.6/` and the new CLI commands (`plan-instances`, `laws`, `typecheck`); Impact: High. Provides an accurate entry point for anyone cloning the repository; Effort: Medium
- **Create a `CONTRIBUTING.md` guide** — Action: Synthesize setup instructions from `README.md`, quality gates from `AGENTS.md`, and testing commands into a single `CONTRIBUTING.md` file; Impact: High. Establishes a single source of truth for the development workflow; Effort: Medium

## References
- [tools/tf-lang-cli/index.mjs](../../../../tools/tf-lang-cli/index.mjs)
- [docs/0.6/index.md](../../../../docs/0.6/index.md)
- [examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml](../../../../examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml)
- [examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json](../../../../examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json)
- [examples/v0.6/](../../../../examples/v0.6)
- [tasks/run-examples.sh](../../../../tasks/run-examples.sh)
- [examples/v0.6/build/auto.quote.bind.issue.v2.l0.json](../../../../examples/v0.6/build/auto.quote.bind.issue.v2.l0.json)
- [scripts/pipeline-expand.mjs](../../../../scripts/pipeline-expand.mjs)
- [schemas/l0-dag.schema.json](../../../../schemas/l0-dag.schema.json)
- [docs/0.6](../../../../docs/0.6)
