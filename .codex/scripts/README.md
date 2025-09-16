Scripts (canonical helpers)

- build-index.py: Build .codex/tasks/INDEX.md from END_GOAL.md bullets.
- check-fixtures-json.ts: Validate JSON under tests/vectors and docs/data.
- collect-run-reports.sh: Fetch PR tips and aggregate run artifacts into .codex/runs and winner anthology.
- compare-reports.mjs: Assert TS vs RS conformance reports match.
- git-clean-refs.sh: Remove PR remotes/refs and sanitize origin refspecs.
- golden.sh: Generate ro-mini output and diff with .golden/ro-mini.out.txt.
- hot-update.sh: One-shot review helper; collects runs and PR bundle into .codex/reviews.
- knowledge.sh: Index .codex/knowledge into docs/runs/knowledge.md.
- lint-briefs.py: Lint .codex/tasks/* for required files and basic YAML sanity.
- lint-vectors.mjs: Lint vector JSON files for version, pointers, and effect shape.
- pack-pass-for-synth.sh: Package PR bodies and AI bot comments (Codex/Gemini) into Markdown and optional PR diffs into JSON. Filters out generic intro posts (Codex "Codex Review: Here are some suggestions.", Gemini "Summary of Changes"). Includes inline review comments from those bots.
- pass-bodies.sh: DEPRECATED — prefer pack-pass + pass-report.
- pass-report.sh: Emit docs/runs/pass-report.md with timestamp and optional GROUP/PRS.
- prbundle.sh: Bundle PR metadata/comments/diffs into one markdown file.
- release-notes.sh: Draft docs/runs/release-notes.md from archive CHANGES.md.
- sync-agents.sh: Sync role blocks into AGENTS.md from .codex/agents/*.
- test-all.sh: Run full TS and Rust test suites.
- test-changed.sh: Pre-push fast path; run only relevant tests.
- winner.sh: Print path to .codex/runs/winner/RUNS_REPORTS.md.

Make targets
- briefs-index, briefs-check, collect-reports, pass-report, pack-pass, winner, knowledge, release-notes, sync-agents, golden, git-clean-refs.
