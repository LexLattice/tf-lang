# Branch {{branchName}}

This branch scaffolds a dual runtime experiment for plan node `{{nodeId}}`.

## Quick start

- Install dependencies: `pnpm install`
- Build JS artifacts: `pnpm -r build`
- Run tf-check oracles: `pnpm tf:check`
- Exercise Rust library: `cargo test`

Artifacts and reports are uploaded via the CI workflow defined in
`.github/workflows/t4-{{branchSlug}}.yml`.
