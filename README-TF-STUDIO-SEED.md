# TF-Studio UI Seed (v0.6)

This pack scaffolds a **shiny, first-impression UI** for TF‑Lang v0.6 with working end-to-end demos.
It includes:

- Next.js app (`apps/tf-studio`) with Tailwind tokens, a hero component (KernelHero), and landing copy.
- Brand splash SVG assets.
- Live API endpoints that import the repo's logic directly (no shelling out):
  - `/api/cli/graph`, `/api/cli/laws`, `/api/cli/effects`, `/api/cli/typecheck`, `/api/cli/plan-instances`, `/api/cli/check`.
  - `/api/cli/expand` (L2 YAML → L0) for the playground editor.
  - `/api/examples/list` for the gallery.
- Minimal client helpers (`lib/tools.ts`) plus interactive surfaces:
  - `/examples` renders curated quick-action cards (Graph + Laws) and links to the full gallery fed by `/api/examples/list`.
  - `/examples/[id]` hosts Graph, Effects, Typecheck, Plan, Laws, and the new Game Master dock on a single screen.
  - `/playground` now combines the CLI helper console with an L2 → L0 editor powered by the expander.
  - `/chat` exposes the Game Master dock for guided checks against a default pipeline.

## Install (monorepo)

1. Unzip at repo root so you get `apps/tf-studio/**`.
2. Add the app to your workspace (pnpm): in `pnpm-workspace.yaml` include `apps/*` if not already.
3. From repo root:
   ```bash
   pnpm install
   pnpm --filter tf-studio dev
   ```
4. Open http://localhost:3000 (or whichever port Next selects if 3000 is busy).

## Quick smoke

- Graph:
  ```bash
  curl -sS -X POST localhost:3000/api/cli/graph     -H 'content-type: application/json'     -d '{"filePath":"examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json"}' | jq .dot | head -n 20
  ```

- Laws (JSON + optional counterexample):
  ```bash
  curl -sS -X POST localhost:3000/api/cli/laws     -H 'content-type: application/json'     -d '{"filePath":"examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json","goal":"branch-exclusive","maxBools":6}' | jq .status,.laws.branch_exclusive.results[0]
  ```

## Notes

- The API layer **does not shell out**; it imports ESM modules from the repo at runtime.
- Paths are restricted to `examples/**` (and `policy/**` for allow‑lists).
- Graph requests default to `strict=false` so external inputs (like `Memory`) render without extra flags; override by passing `strict: true`.
- `/examples`, `/examples/[id]`, `/playground`, and `/chat` are safe client sandboxes that only call the in-repo API routes—use them as templates for richer flows.
- Follow the same `webpackIgnore` pattern when adding more endpoints so Next doesn’t bundle large ESM modules.
