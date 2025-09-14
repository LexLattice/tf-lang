# Pages Preview and Deploy

This repository builds the `docs/` folder on every PR and deploys it to
GitHub Pages from `main`.

## Workflow
- PRs: job `pages / build` uploads a Pages artifact from `docs/` using
  `actions/upload-pages-artifact@v3`.
- `main`: job `pages / deploy` publishes the artifact to the Pages environment
  via `actions/deploy-pages@v4`.

See `.github/workflows/pages.yml` for the exact steps and permissions.

## Preview (from a PR)
- Open the PR → Checks → workflow “pages”.
- In the `build` job, download the artifact named “github-pages” (default) to
  preview the static site locally.

Notes:
- Only the `docs/` folder is included in the artifact.
- There is no remote “preview URL” for PRs; artifacts are downloadable only.

## Deploy (on main)
- Merging to `main` triggers the `deploy` job, which updates the Pages site.
- The environment `github-pages` exposes the live URL. GitHub also shows the
  `page_url` output in the job summary.

Live site: https://LexLattice.github.io/tf-lang/

## Status and badges
- A badge at the top of `README.md` links to the Pages workflow and the live
  site:
  `[![deploy](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml/badge.svg?branch=main)](https://LexLattice.github.io/tf-lang/)`.
- The Actions tab shows the latest `pages` runs for both PRs and `main`.

