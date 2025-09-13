# Git PR Refs Cleanup

Why refs appear: past tooling fetched PR tips into persistent local/remote-tracking refs (e.g., codex/pr-*, origin/pr/*), cluttering branch pickers.

Run once to purge and sanitize: `make git-clean-refs`.

Ongoing hygiene: collectors now fetch PRs ephemerally (FETCH_HEAD) and never create local refs. VS Code also prunes on fetch via `.vscode/settings.json`.

Safe anytime: re-run `make git-clean-refs` to prune stale refs/tags and ensure `.git/config` has no PR refspecs.
