# Track F — Release & DevEx Quickstart

Sweep repo health: audits, determinism probes, and doc link checks that gate releases.

## Prerequisites

- Workspace install (`pnpm -w -r install --frozen-lockfile`)
- `bash`, `node`, and `npx` available
- Network access for npm to fetch the link checker

## Commands (3–7 steps)

```bash
OUT=out/0.5/devex
mkdir -p "$OUT"
pnpm run audit > "$OUT/audit.json"
pnpm run determinism > "$OUT/determinism.log"
pnpm run docs:check -- docs/0.5/overview.md > "$OUT/link-check.txt"
tail -n 5 "$OUT/link-check.txt"
```

## Expected output

```
{ "ok": true, "determinism": { "ok": true, "issues": [] } }
Determinism OK
  [✓] quickstarts/track-e-proofs.md
  [✓] quickstarts/track-f-release-devex.md
  13 links checked.
```

*Audits surface newline/exec-bit drift (`missing_newline`, `missing_exec`); determinism probes rerun `a0` twice to confirm identical digests. The Markdown link checker must finish cleanly before docs ship.*

## Where next?

- Audit implementation details: [`scripts/audit/run.mjs`](../../../scripts/audit/run.mjs)
- Determinism harness internals: [`scripts/determinism-check.sh`](../../../scripts/determinism-check.sh)
- Documentation linting CI: [`.github/workflows/l0-docs.yml`](../../../.github/workflows/l0-docs.yml)

> **Troubleshooting**
>
> - `pnpm run audit` exits non-zero – inspect the JSON under `determinism.issues`; rerun after fixing newline/exec flags.
> - `pnpm run docs:check -- docs/0.5/overview.md` reports broken quickstart links – ensure every target exists and uses relative paths (`../` for parent dirs).
> - Determinism probe fails – rerun `pnpm run a0` manually; uncommitted changes in `out/**` often cause mismatched digests.
