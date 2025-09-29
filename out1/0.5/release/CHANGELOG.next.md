# CHANGELOG.next

## Features
- Add single-file L0 runtime CLI in `packages/tf-lang-l0-ts` (`out/0.5/review-jules/B-Runtime/docs.jules.md`).
- Expose pass toggles like `--disable-pass` in `packages/tf-opt` (`out/0.5/review-jules/D-Optimizer/docs.jules.md`).
- Ship a `pnpm tf-trace` entrypoint via proper `bin` wiring (`out/0.5/review-jules/C-Trace-Perf/docs.jules.md`).
## Fixes
- Fix the missing export that breaks `tf-opt --help` (`out/0.5/review-jules/D-Optimizer/docs.jules.md`).
- Auto-build `@tf-lang/tf-trace` on install to avoid missing dist assets (`out/0.5/review-jules/C-Trace-Perf/docs.jules.md`).
## Chore
- _No changes._
## Docs
- Publish a VS Code LSP quickstart and DSL expectations in `clients/vscode-tf` and `docs/language.md` (`out/0.5/review-jules/A-LSP-DSL/docs.jules.md`).
- Document the runtime Host contract and execution model in `packages/tf-lang-l0-ts` (`out/0.5/review-jules/B-Runtime/docs.jules.md`).
- Add a proofs runner guide with Z3 setup to `packages/tf-l0-proofs` (`out/0.5/review-jules/E-Proofs/docs.jules.md`).
- Explain the docs index pipeline in `scripts/docs/README.md` (`out/0.5/review-jules/F-DevEx-Release/release-readiness.jules.md`).
## CI
- Teach `tools/release/changelog.mjs` to categorize commits into Features/Fixes/Docs (`out/0.5/review-jules/F-DevEx-Release/release-readiness.jules.md`).
- Add a release verification job that asserts `pack.json` contents and changelog health (`out/0.5/review-jules/F-DevEx-Release/release-readiness.jules.md`).
- Gate trace budgets in CI with `tf-trace --fail-on-violation` (`out/0.5/review-jules/C-Trace-Perf/docs.jules.md`).
## Other
- Apply patch /tmp/8858193f-95a2-4960-a560-fb58f66a0da7.patch (580898f)
- node:F-DevEx-Release cp:cp5_docs_gate (#311) (75a1a9e)
