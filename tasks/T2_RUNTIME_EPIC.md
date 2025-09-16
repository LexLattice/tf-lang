# T2_RUNTIME_EPIC — Runtime + Tooling (CLI, Adapters, Mapper, Coverage)

Covers: **T2_1 tf-check (TS CLI)**, **T2_2 Adapters (TS+Rust)**, **T2_3 Trace→Tags mapper (TS)**, **T2_4 Coverage generator (TS)**, **T2_5 CI wiring**.

## ACCEPTANCE

### Evidence
- TS packages:
  - `packages/tf-check/` (CLI with help, deterministic behavior)
  - `packages/adapters/ts/execution/` (TS execution adapter)
  - `packages/mapper/trace2tags/` (trace→tags)
  - `packages/coverage/generator/` (coverage rollup from tags)
- Rust crates:
  - `crates/adapters/execution/` (Rust execution adapter with parity tests)
- Docs:
  - `docs/tf-check/USAGE.md`, `docs/trace-schema.md`, READMEs in each package
- Artifacts:
  - `out/t2/tf-check/help.txt`, `out/t2/tf-check/result.json`
  - `out/t2/trace-tags.json`
  - `out/t2/coverage.json`, `out/t2/coverage.html`
  - (optional) `out/t2/adapter-parity.json`

### CI
Jobs (authoritative names):
- **`tf-check-cli`** — builds/runs CLI, prints `--help` to `out/t2/tf-check/help.txt`, validates a small sample and writes `out/t2/tf-check/result.json`.
- **`adapter-ts`** — builds TS execution adapter + unit/property tests.
- **`adapter-rust`** — builds Rust execution adapter + unit/property tests.
- **`mapper-trace2tags`** — runs the mapper on stored traces to produce `out/t2/trace-tags.json`.
- **`coverage-report`** — consumes tags to produce `out/t2/coverage.(json|html)`.
- (if both adapters built) **`adapter-parity`** — runs the same sample via both runtimes and writes `out/t2/adapter-parity.json` (structural parity).

Each job runs offline, deterministic, uploads its artifacts under `out/t2/…`.

### Determinism
Use canonical JSON for all outputs. Record seeds if any randomized tests occur. Lock `now` in tests.

### Docs
Each package includes a short README; `docs/tf-check/USAGE.md` documents CLI flags and exit codes; `docs/trace-schema.md` documents mapper IO.

### PR Body (required)
Follow `.github/pull_request_template.md`. CI enforces presence of required sections.

## BLOCKERS (policy)
- `schema_changes_allowed: false`
- Must not: cross-test state or nondeterminism; introduce runtime deps (dev deps OK), change public APIs beyond epic scope; gate merges on local hooks.
- Machine rules: TS (`no_deep_imports`, `internal_esm_imports_end_with_js`, `no_as_any`); Rust (`no_static_mut`, `no_panicking_unwraps_in_libs`, `use_atomics_mutexes_appropriately`); `runtime_deps: {allowed:false, ci_dev_deps_allowed:true}`.

## END_GOAL (workplan)
1) **T2_1 tf-check (TS)**: scaffold CLI, implement `--help`, `validate` subcommand over a tiny fixture set; produce `help.txt`, `result.json`.
2) **T2_2 Adapters**: TS execution adapter; Rust adapter parity as time allows; property tests for inputs/outputs.
3) **T2_3 Mapper**: parse traces; map to TF tags; write `trace-tags.json` (documented by `docs/trace-schema.md`).
4) **T2_4 Coverage**: compute coverage from tags; emit `coverage.json` + a tiny static `coverage.html`.
5) **T2_5 CI**: wire jobs above; artifacts uploaded; determinism re-run step.

## EVIDENCE INDEX
- CLI: `packages/tf-check/`
- Adapters: `packages/adapters/ts/execution/`, `crates/adapters/execution/`
- Mapper: `packages/mapper/trace2tags/`
- Coverage: `packages/coverage/generator/`
- Docs: `docs/tf-check/USAGE.md`, `docs/trace-schema.md`
