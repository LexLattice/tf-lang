# Review: F-DevEx-Release (v0.5)

This document reviews the release process and developer experience for Track F (DevEx-Release). It's based on a local dry-run of the `.github/workflows/release.yml` workflow.

## 1. Release Dry-Run Walkthrough

The release process is orchestrated by a series of scripts, designed to be run in CI. Here’s a summary of each step.

### Step 1: Lockfile Guard (`lockfile-guard.mjs`)

- **What it does:** This script checks if the `pnpm-lock.yaml` file is in sync with the `package.json` files across the monorepo. It ensures that no dependency changes have been made without being properly reflected in the lockfile.
- **Why it matters:** A consistent lockfile is critical for reproducible builds. This check prevents "works on my machine" issues by guaranteeing that CI and local development environments use the exact same dependency versions.
- **How it fails usefully:** If the lockfile is outdated, the script exits with a non-zero status code and prints a JSON object indicating `{"ok":false}`. In CI, this immediately fails the release job, preventing a release with unstable dependencies.

```bash
# How to run it locally:
node tools/ci/lockfile-guard.mjs --json

# "What good looks like" (log snippet):
# {"ok":true,"changed_packages":[],"lockfile_changed":false,"ignored_prefixes":["vendor/","third_party/"]}
```

### Step 2: Pack Manifest (`pack-all.mjs`)

- **What it does:** This script simulates the `pnpm pack` process for all public packages in the workspace (i.e., those without `"private": true` in their `package.json`). It generates a manifest (`out/0.5/release/pack.json`) that lists every package to be published.
- **What's included/skipped:** Only packages intended for the public registry are included. Private packages, like internal tools or example apps, are correctly ignored. The manifest lists the package name, version, and directory.
- **Why it matters:** This step provides a clear, auditable record of what will be part of the release. It allows for a final check to ensure no private or unintended packages are accidentally published.

```bash
# How to run it locally:
node tools/release/pack-all.mjs

# "What good looks like" (log snippet):
# {
#   "ok": true,
#   "output": "out/0.5/release/pack.json",
#   "checksum": "...",
#   "packages": 23
# }
```

### Step 3: Changelog Generator (`changelog.mjs`)

- **What it does:** The script scans the Git history since the last tag and generates a draft changelog file (`out/0.5/release/CHANGELOG.next.md`).
- **Sectioning rules:** It appears to categorize commits based on conventional commit prefixes (e.g., `feat:`, `fix:`, `docs:`), but the current output shows most changes under "Other". This suggests the commit history doesn't strictly follow the convention or the script's parsing rules are loose.
- **How to include/exclude:** Since it's based on Git history, inclusion is determined by what has been merged. There's no clear mechanism to manually exclude a specific commit from the generated notes, other than amending the commit message itself.

```bash
# How to run it locally:
node tools/release/changelog.mjs

# "What good looks like" (log snippet):
# {
#   "ok": true,
#   "file": "out/0.5/release/CHANGELOG.next.md"
# }
```

### Step 4: Docs Build Stub (`scripts/docs/build.mjs`)

- **What it does:** This script appears to generate a JSON index of documentation artifacts. It creates `out/0.5/docs/index.json`.
- **What consumes it:** The purpose isn't fully clear from the file itself, but this type of structured data is typically consumed by a downstream process, such as a static site generator (e.g., Docusaurus, Next.js) that builds the final documentation website.

```bash
# How to run it locally:
node scripts/docs/build.mjs

# "What good looks like" (log snippet):
# {"ok":true,"output":"out/0.5/docs/index.json"}
```

### Step 5: CI Workflow (`.github/workflows/release.yml`)

- **Dry-run entry point:** The workflow is triggered manually via `workflow_dispatch`, making it safe for dry-runs.
- **Composite Action:** It uses a reusable action (`./.github/actions/setup-pnpm`) to ensure a consistent Node.js and pnpm environment. The `frozen: 'true'` parameter is key—it enforces the use of `pnpm install --frozen-lockfile`, which is the rationale for the `lockfile-guard` check. If the lockfile is not perfectly in sync, this installation step will fail fast.

## 2. Gaps & DX Friction

1.  **Changelog Grouping:** The changelog generator is too coarse. Nearly all commits are bucketed under "Other," which reduces the utility of the generated notes. The logic should be refined to better parse conventional commit types.
2.  **Docs Consumer Unclear:** The purpose and downstream consumer of the `docs/index.json` file are not documented. A new developer would have no context on how to use this artifact or troubleshoot its generation.
3.  **Noisy `pack.json`:** The `pack.json` manifest includes many internal-only packages (e.g., `@tf-lang/tf-plan-core`) that are not true end-user libraries. While they aren't marked `private`, the distinction between "public library" and "public internal dependency" is blurry.
4.  **Missing Verification:** The dry-run successfully *generates* artifacts, but it doesn't *verify* them. For example, it doesn't check that the generated `pack.json` contains the expected packages or that the changelog is non-empty.

## 3. Next 3 Improvements

1.  **(M) Refine Changelog Script:** Improve the commit parsing logic in `changelog.mjs` to correctly categorize commits into `Features`, `Fixes`, `Docs`, etc. Add a `README.md` explaining the expected commit message format.
2.  **(S) Document the Docs Pipeline:** Add a `README.md` in `scripts/docs/` that explains the purpose of `build.mjs`, what `index.json` is for, and which downstream CI/CD job consumes it.
3.  **(L) Add Release Verification:** Extend the `release.yml` workflow with a "verify" job that runs after "pack". This job could run basic checks, such as asserting that `pack.json` contains a specific, critical package (e.g., `@tf-lang/tf-lsp-server`) and that `CHANGELOG.next.md` contains more than just empty sections.