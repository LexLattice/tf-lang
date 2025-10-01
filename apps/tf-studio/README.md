# TF-Studio (UI) — v0.6

A shiny, first-impression UI for TF-Lang v0.6 covering the gallery, deep example detail, playground, and a minimal Game Master.

## Run
```bash
pnpm install
pnpm --filter tf-studio dev
# http://localhost:3000
```

## Highlights
- Gallery (`/examples`) backed by `/api/examples/list`, plus quick-action cards that hit the graph/law CLI endpoints directly.
- Example detail (`/examples/[id]`) with Graph, Effects, Typecheck, Instance Plan, Laws, and the Game Master dock on one screen.
- Playground (`/playground`) combines the console-style helpers with an L2 → L0 expansion editor.
- Game Master (`/chat`) exposes the interactive dock for guided checks against a default pipeline.

## Notes
- API endpoints import repo ESM modules directly (no shelling out) using `webpackIgnore` to avoid bundling.
- Paths are restricted to `examples/**` (and `policy/**` for law/policy lookups).
- Set `NEXT_PUBLIC_BASE_URL` if you proxy through a different origin.
```
