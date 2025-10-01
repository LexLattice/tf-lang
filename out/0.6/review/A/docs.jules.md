# Track A: Platform Scaffolding

## What exists now

*   **Schemas**: A comprehensive set of JSON schemas under `schemas/` defines core data structures, including `l2-pipeline`, `l0-dag`, `effects`, `manifest`, and `law`. Schemas for older versions (v0.4) are present alongside current ones.
*   **CLI**: The primary CLI entry point is `tools/tf-lang-cli/index.mjs`. It exposes commands for validation, effects analysis, graph generation, type checking, instance planning, and law verification. Help is available via the `--help` flag.
*   **Documentation**: High-level guidance is in `AGENTS.md`. The root `README.md` is for v0.5. A v0.6-specific doc (`docs/0.6/index.md`) exists but notes that detailed specification pages are missing.
*   **CI**: GitHub Actions workflows are defined for key quality gates, including runtime verification, proofs, audits, and doc synchronization, as linked in the `README.md`.

## How to run

Key platform commands focus on validation and introspection.

*   **View available commands**:
    ```bash
    node tools/tf-lang-cli/index.mjs --help
    ```

*   **Validate an L2 pipeline definition**:
    ```bash
    node tools/tf-lang-cli/index.mjs validate l2 examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
    ```

*   **Validate an L0 build artifact**:
    ```bash
    node tools/tf-lang-cli/index.mjs validate l0 examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
    ```

## Common errors + fixes

*   **Error**: `unable to infer schema; pass l0 or l2 explicitly`
    *   **Cause**: Running `validate` without specifying the language level (`l0` or `l2`).
    *   **Fix**: Add the `l0` or `l2` subcommand after `validate`.

## Gaps

1.  **DX Friction (CLI)**: Commands are verbose (`node tools/tf-lang-cli/index.mjs ...`). The `pnpm install` log shows warnings that shorter aliases (e.g., `tf-plan`) failed to be created, indicating a broken or incomplete setup in `package.json`.
2.  **Documentation (Onboarding)**: The root `README.md` is for v0.5 and does not reflect the v0.6 tools and examples. This creates immediate confusion for new contributors.
3.  **Documentation (Gaps)**: `docs/0.6/index.md` explicitly states that detailed v0.6 specification pages are missing. There is no central `CONTRIBUTING.md` to guide new developers on workflow, setup, and testing.
4.  **Schema Versioning**: The presence of v0.4 schemas alongside current schemas in `schemas/` can lead to confusion about which to reference.

## Next 3 improvements

1.  **Fix and consolidate CLI aliases.**
    *   **Action**: Correct the `bin` entries in the relevant `package.json` to create simple aliases like `tf`, so commands become `tf validate ...`.
    *   **Impact**: High. Drastically improves CLI ergonomics and discoverability, making local development faster.
    *   **Effort**: Small.

2.  **Update the root `README.md` for v0.6.**
    *   **Action**: Replace v0.5 content with a v0.6-centric quickstart, pointing to `examples/v0.6/` and the new CLI commands (`plan-instances`, `laws`, `typecheck`).
    *   **Impact**: High. Provides an accurate entry point for anyone cloning the repository.
    *   **Effort**: Medium.

3.  **Create a `CONTRIBUTING.md` guide.**
    *   **Action**: Synthesize setup instructions from `README.md`, quality gates from `AGENTS.md`, and testing commands into a single `CONTRIBUTING.md` file.
    *   **Impact**: High. Establishes a single source of truth for the development workflow.
    *   **Effort**: Medium.