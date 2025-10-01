# Track A · Platform scaffolding

## What exists now
- **CLI surface**: `tf` entrypoint (`tools/tf-lang-cli/index.mjs`) covers schema validation, effect summaries, DOT graphing, typecheck, instance planning, and law checks with a single usage banner.
- **Schema set**: `schemas/` includes L0 DAG, L2 pipeline, catalog/effects, manifests, and capability/type scaffolds reused by expander + checker flows.
- **Docs footprint**: v0.5 overview + quickstarts remain; v0.6 landing page lists example pipelines/monitors and macro law notes but auto-generated spec pages are empty.
- **Tasks**: `tasks/run-examples.sh` meant as the 10-min smoke for v0.6 (build → lint → diagrams) invoking CLI helpers + bespoke assertions.

## How to run
1. Install workspace deps once: `pnpm install --frozen-lockfile`.
2. Validate existing artifacts:
   - Schema check (currently fails for transforms with structured `in` bindings): `node tools/tf-lang-cli/index.mjs validate examples/v0.6/build/auto.quote.bind.issue.v2.l0.json`.
   - Effects summary: `node tools/tf-lang-cli/index.mjs effects <L0>`.
   - DOT graph: `node tools/tf-lang-cli/index.mjs graph <L0> > diagrams/<name>.dot` and optionally `dot -Tsvg …`.
3. Ten-minute intended flow: `bash tasks/run-examples.sh` (expands pipelines + monitors, runs spec scripts, emits diagrams) — currently exits on inline macro comments.

## Common errors + fixes
- `tf validate` reports `data/nodes/*/in must be string/null` on v0.6 builds: schema still reflects v0.5 scalar input form. Workaround: skip schema validation or downgrade transforms before release.
- `bash tasks/run-examples.sh` aborts with `invalid call syntax … # types:` because the expander does not strip trailing YAML comments. Hand-edit pipelines or run `node scripts/pipeline-expand.mjs` after removing inline `# types` hints.
- New contributors land in v0.5 docs; no 0.6 quickstart exists yet. Point them at `docs/0.6/index.md` manually and explain missing spec content.

## Gaps
- Schema + docs drift from 0.6 kernel shape (structured transform inputs, monitors bundle) blocks validation + onboarding.
- Quickstart script fails out-of-the-box; no happy path to see a green build.
- `docs/0.6/index.md` references empty spec and lacks per-track gate summaries.

## Next 3 improvements
1. Regenerate `schemas/l0-dag.schema.json` + CLI validator to accept object `in` bindings and monitor bundles, then document the new expectations.
2. Teach expander preprocessing to strip trailing `#` comments (or sanitize when quoting macros) so `tasks/run-examples.sh` succeeds without manual edits.
3. Publish a v0.6 quickstart (README patch + docs/0.6) listing install → run-examples → law + plan commands with troubleshooting snippets.
