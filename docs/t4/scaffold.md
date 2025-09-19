# T4.2 — Parallel Branch Scaffolder

The T4 scaffolder builds reproducible branch plans from `tf-plan` outputs, maps
plan nodes to branch names, and wires baseline CI for apples-to-apples checks.

## Generating a scaffold plan

```bash
pnpm --filter @tf-lang/tf-plan run build
pnpm --filter @tf-lang/tf-plan-scaffold run build
node packages/tf-plan-scaffold/dist/cli.js scaffold \
  --plan out/t4/plan/plan.ndjson \
  --template dual-stack \
  --top 3 \
  --out out/t4/scaffold/index.json
```

This command reads the enumerated plan graph, selects the top candidates, and
writes a deterministic scaffold plan at `out/t4/scaffold/index.json`.

## Applying a scaffold plan

```bash
node packages/tf-plan-scaffold/dist/cli.js scaffold \
  --apply out/t4/scaffold/index.json
```

Applying a plan creates branches if missing, syncs the template workdir into the
branch worktree path, and updates repository scripts (e.g. `pnpm tf:check`).

Use `--dry-run` to validate the plan without writing to disk.

## Opening draft PRs

```bash
node packages/tf-plan-scaffold/dist/cli.js pr \
  --plan out/t4/scaffold/index.json \
  --open-draft
```

Draft mode calls the GitHub CLI (`gh`) per branch; omit `--open-draft` to print
PR metadata without opening anything.

## Template packs

Templates live under `templates/t4/<name>` and consist of:

- `template.json` — metadata describing workdir files, CI workflows, and package
  scripts.
- `workdir/` — files copied into each branch-specific worktree (placeholders such
  as `{{branchName}}` are rendered deterministically).
- `ci/` — reusable workflow definitions and per-branch workflow templates.

The `dual-stack`, `ts`, and `rs` packs provide ready-to-run scaffolds for
TypeScript+Rust, TypeScript-only, and Rust-only experiments respectively.
