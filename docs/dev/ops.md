Dev Ops Cheatsheet

- collect-reports: aggregate parallel runs into `.codex/runs/winner/RUNS_REPORTS.md`.
- pass-report: emit a pass summary under `docs/runs/pass-report.md`.
- pack-pass: package pass outputs to `docs/runs/pack-pass/`.
- winner: print path to the winner anthology file.
- knowledge: index `.codex/knowledge` into `docs/runs/knowledge.md`.
- release-notes: draft release notes into `docs/runs/release-notes.md`.
- sync-agents: sync role blocks into `AGENTS.md`.
- git-clean-refs: remove stale PR refspecs from git config.

All helper scripts live in `.codex/scripts/`. Outputs under `docs/runs/`.
