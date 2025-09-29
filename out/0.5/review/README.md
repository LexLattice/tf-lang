# TF Lang 0.5 Milestone Review

## Status matrix

| Track | Acceptance | Perf baseline (ms) | Open blockers |
| --- | --- | --- | --- |
| A — LSP Proto & DSL | RED | TBD | 3 |
| B — Runtime | RED | TBD | 2 |
| C — Trace & Perf | RED | >30000 (summary on 5M rows) | 1 |
| D — Optimizer | RED | TBD | 2 |
| E — Proofs | RED | TBD | 2 |
| F — DevEx & Release | RED | TBD | 0 |

## Track directory

- **Track A — LSP Proto & DSL Ergonomics**: quick-fix templates and lexer gaps break authoring flows on large specs. [Findings](./A/findings.codex.md) · Rulebooks [A1-LSP-Proto](../../tf/blocks/A1-LSP-Proto/rulebook.yml), [A4-DSL-Ergonomics](../../tf/blocks/A4-DSL-Ergonomics/rulebook.yml). Acceptance phases: `cp1_baseline → cp4_code_actions` (A1), `cp1_syntax → cp4_refactors` (A4).
- **Track B — Runtime**: WASM shims corrupt traces and enumeration crashes on novel ops. [Findings](./B/findings.codex.md) · Rulebook [B1-B2-Runtime](../../tf/blocks/B1-B2-Runtime/rulebook.yml). Acceptance phases: `cp1_scaffold → cp3_parity_smoke`.
- **Track C — Trace & Perf**: Trace ingestion, budgets, and exports incur high memory churn and reject extensibility. [Findings](./C/findings.codex.md) · Rulebook [C-Trace-Perf](../../tf/blocks/C-Trace-Perf/rulebook.yml). Acceptance phases: `cp1_schema → cp5_perf_gate`.
- **Track D — Optimizer**: Rewrite passes ignore directionality and mutate IR unsafely. [Findings](./D/findings.codex.md) · Rulebook [D1-D2-Optimizer](../../tf/blocks/D1-D2-Optimizer/rulebook.yml). Acceptance phases: `cp1_cost_model → cp2_rewrites`.
- **Track E — Proofs**: Storage laws are unsound and casing mismatches break automation. [Findings](./E/findings.codex.md) · Rulebook [E1-E2-Proofs](../../tf/blocks/E1-E2-Proofs/rulebook.yml). Acceptance phases: `cp1_linkage → cp2_solver_gate`.
- **Track F — DevEx & Release**: Release bundles remain non-deterministic and lack cross-platform coverage. [Findings](./F/findings.codex.md) · Rulebook [F-DevEx-Release](../../tf/blocks/F-DevEx-Release/rulebook.yml). Acceptance phases: `cp1_workflows → cp5_docs_gate`.

## How to re-run acceptance probes

### Track A1 — LSP Proto
- `cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff - --allow "pnpm-lock.yaml"`
- `pnpm -C packages/tf-lsp-server install --no-frozen-lockfile --prefer-offline`
- `node packages/tf-lsp-server/bin/server.mjs --stdio` *(spawned via scripts for LSP smoke tests)*
- `pnpm -C packages/tf-lsp-server run build`
- `node scripts/lsp-smoke/stdio.mjs --mode init`
- `node packages/tf-compose/bin/tf.mjs parse samples/a1/illegal_write.tf -o out/0.45/a1/parse.json`
- `cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`
- `cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff - --forbid "pnpm-lock.yaml"`
- `bash -lc 'test -z "$(git diff --cached --name-only -- samples/a1/** scripts/lsp-smoke/**)"'`
- `node scripts/lsp-smoke/stdio.mjs --mode diagnostics --file samples/a1/protected_write.tf`
- `node scripts/lsp-smoke/stdio.mjs --mode diagnostics --file samples/a1/syntax_error.tf`
- `node scripts/lsp-smoke/stdio.mjs --mode hover --file samples/a1/illegal_write.tf --symbol "tf:network/publish@1"`
- `cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`
- `node scripts/lsp-smoke/stdio.mjs --mode codeAction --file samples/a1/protected_write.tf`
- `TF_STRICT=1 cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`
- `TF_STRICT=1 cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`

### Track A4 — DSL Ergonomics
- `cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`
- `node packages/tf-compose/bin/tf.mjs parse samples/a4/let_basic.tf -o out/0.45/a4/let.json`
- `node --test packages/tf-compose/src/tests/let-include.test.mjs`
- `node packages/tf-compose/bin/tf.mjs check samples/a4/let_shadow.tf`
- `node packages/tf-compose/bin/tf.mjs check samples/a4/let_ok.tf`
- `node --test packages/tf-compose/src/tests/let-canon.test.mjs`
- `node packages/tf-compose/bin/tf.mjs parse samples/a4/root_with_include.tf --base samples/a4 -o out/0.45/a4/include-expanded.json`
- `node packages/tf-compose/bin/tf.mjs parse samples/a4/include_cycle_root.tf --base samples/a4`
- `node scripts/lsp-smoke/stdio.mjs --mode codeAction --file samples/a4/dup_expr.tf`
- `node scripts/lsp-smoke/stdio.mjs --mode codeAction --file samples/a4/let_decl.tf`

### Track B — Runtime
- `cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`
- `pnpm -C packages/tf-run-wasm install --no-frozen-lockfile && pnpm -C packages/tf-run-wasm build`
- `node packages/tf-run-wasm/bin/cli.mjs --help`
- `bash -lc 'command -v cargo >/dev/null 2>&1 && cargo --version && echo "[wasm] building" && exit 0 || exit 0'`
- `node packages/tf-run-wasm/bin/cli.mjs --ir out/0.4/ir/signing.ir.json --status out/0.5/wasm/status.json --trace out/0.5/wasm/trace.jsonl`
- `node scripts/wasm/compare-traces.mjs --a tests/fixtures/trace-sample.jsonl --b out/0.5/wasm/trace.jsonl`

### Track C — Trace & Perf
- `node packages/tf-trace/bin/trace.mjs validate --in samples/c/trace_small.jsonl`
- `node packages/tf-trace/bin/trace.mjs summary --in samples/c/trace_small.jsonl --out out/0.5/trace/summary.json`
- `node packages/tf-trace/bin/trace.mjs budget --in samples/c/trace_small.jsonl --spec tf/blocks/C-Trace-Perf/budgets.sample.json`
- `node packages/tf-trace/bin/trace.mjs export --in samples/c/trace_small.jsonl --csv out/0.5/trace/trace.csv`
- `node packages/tf-trace/bin/trace.mjs budget --in samples/c/trace_small.jsonl --spec tf/blocks/C-Trace-Perf/budgets.sample.json`
- `TF_STRICT=1 cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`

### Track D — Optimizer
- `cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`
- `node packages/tf-opt/bin/opt.mjs --help`
- `node packages/tf-opt/bin/opt.mjs --cost show`
- `node packages/tf-opt/bin/opt.mjs --ir out/0.4/ir/signing.ir.json -o out/0.5/opt/signing.plan.json`
- `node packages/tf-opt/bin/opt.mjs --ir out/0.4/ir/signing.ir.json --emit-used-laws out/0.5/proofs/used-laws.json`

### Track E — Proofs
- `node packages/tf-opt/bin/opt.mjs --ir out/0.4/ir/signing.ir.json --emit-used-laws out/0.5/proofs/used-laws.json`
- `node scripts/proofs/ci-gate.mjs --check-used out/0.5/proofs/used-laws.json`
- `node scripts/proofs/ci-gate.mjs --small samples/e1/small_flow.tf`

### Track F — DevEx & Release
- `bash -lc "node -e \"process.env.CI='true';console.log('ok')\" >/dev/null; grep -En -- \"pnpm install --frozen-lockfile\" .github/actions/setup-pnpm/action.yml && ! grep -En -- \"frozen.*--no-frozen-lockfile\" .github/actions/setup-pnpm/action.yml && grep -En -- \"pnpm install --no-frozen-lockfile\" .github/actions/setup-pnpm/action.yml"`
- `bash -lc "test -f .github/workflows/release.yml && echo ok"`
- `node tools/ci/lockfile-guard.mjs`
- `node tools/release/pack-all.mjs`
- `node tools/release/changelog.mjs`
- `node scripts/docs/build.mjs`
- `TF_STRICT=1 cat "$DIFF_PATH" | node tools/tf-checker/scan-diff.mjs --config meta/checker.yml --diff -`
