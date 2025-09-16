# T2 Research Notes — CLI, Paths, Utils

## Scope
Requested follow-up review of items raised across PRs #113–#116. For each, I checked whether the change already exists on this branch, whether there is an alternate PR to cherry-pick from, and the best implementation path if missing. Tests/builds run earlier in this session are noted where relevant.

---

## 1. CLI: correctness & UX

| Item | Status in current branch | Alternate PR? | Recommendation |
| --- | --- | --- | --- |
| Allow empty string option values in tf-check CLI | **Missing.** `parseFlagArgs` still rejects inline values with `inline.length === 0` and treats the next token `""` as falsy (line 37). | The behaviour was proposed in #113, but I don't see an equivalent change merged here. No local commit to cherry-pick. | Update `parseFlagArgs` to treat `""` as a valid value: replace `if (inline.length === 0)` with a check for `inline === undefined`, and change the positional branch to check `next === undefined` rather than `!next`. Add/extend CLI tests accordingly. |
| Remove/bypass direct-execution guard | **Implemented.** The guard was removed and `main()` now runs unconditionally (`packages/tf-check/src/cli.ts:121`). | n/a | No action needed. |
| Support `-h/--help` when passed to subcommands | **Missing.** Only top-level help is supported; subcommand `parseFlagArgs` lists do not include `-h/--help`. | Not present locally; proposed in #114. | Extend `parseFlagArgs` to accept a secondary list of valueless flags (e.g., `["--help", "-h"]`), returning a structured result (flags + options) so callers can exit cleanly. Update CLI tests. |

Tests: `pnpm --filter @tf-lang/tf-check run build` executed successfully after earlier fixes; once parser is updated, rerun the same command plus targeted Vitest suites.

---

## 2. Paths & repo-root resolution

| Item | Status | Alternate PR? | Recommendation |
| --- | --- | --- | --- |
| Replace `URL.pathname` with `fileURLToPath` | **Partially done.** Artifacts modules now decode URLs, but `packages/adapters/ts/execution/src/parity.ts` still uses `.pathname`. There may be other stragglers outside T2, e.g., `packages/adapter-legal-ts/...`. | The parity change was highlighted in #113/#114; not present here. | Update remaining modules (at minimum T2 parity) to use `fileURLToPath(new URL('.', import.meta.url))`. |
| Anchor tf-check artifacts dir to repo root | **Not yet addressed.** `runArtifacts` defaults to `path.resolve("out/t2/tf-check")` (line 81). | Mentioned in #115; no local change. | Compute once using `findRepoRoot(fileURLToPath(...))` (similar to artifacts.ts) and use it as the default out dir. |

Tests: We’ve run `pnpm --filter @tf-lang/trace2tags run artifacts` and `pnpm --filter @tf-lang/adapter-execution-ts run build`; after the path fixes, rerun those commands to confirm the repo-root lookups still succeed.

---

## 3. `@tf-lang/utils`

| Item | Status | Alternate PR? | Recommendation |
| --- | --- | --- | --- |
| Use `Object.fromEntries` in `canonicalize` | **Not yet.** The code still builds a manual object (lines 11–17). | Suggested in #113/#116; not applied. | Replace the manual loop with `return Object.fromEntries(entries)` and use `localeCompare` for key sorting. |
| Harden `isObject` guard | **Missing.** No helper exists; arrays are excluded earlier but the guard requested for future-proofing isn’t present. | Proposed in #114. | Introduce `isPlainObject` helper and reuse it to enter the object branch. |
| Escape `/` in `escapeHtml` | **Missing.** Map/regex omit `/`. | Suggested in #116. | Add `/` to the map and regex. |

Tests: `pnpm --filter @tf-lang/trace2tags run build` and `pnpm --filter @tf-lang/tf-check run build` already exercise canonicalization/escaping indirectly; extend unit tests in `packages/utils/tests` to cover the new cases (empty string values, `/` escaping, non-object guard).

---

## 4. Tests & parity gates

- XSS regression: the existing coverage generator tests still pass (`pnpm --filter @tf-lang/trace2tags run artifacts` depends on the HTML generation). No changes needed besides maintaining coverage once `/` escaping is added.
- CLI parser tests: add cases for `--out=""`, `--help` on subcommands, and unknown short flags. Existing Vitest targets should catch regressions.
- Repo-root discovery: after replacing `.pathname`, consider adding a unit test or integration test that stubs a path with spaces to ensure `findRepoRoot` handling remains correct (manual testing on the Windows runner is still advisable).
- Parity tmp cleanup: logic already lives in utils (`withTmpDir`) and parity harness; current parity build succeeded, so no additional action unless new changes affect it.

---

## Summary / Next Steps

1. Implement the remaining CLI parser improvements (empty strings, per-command help) and add tests.
2. Finish URL decoding: update parity.ts (and any other stragglers) and make tf-check artifacts default to the repo-root path.
3. Polish `@tf-lang/utils`: adopt `Object.fromEntries`, add a plain-object guard, and extend the HTML escape map.
4. After applying the above, rerun:
   - `pnpm --filter @tf-lang/tf-check run build`
   - `pnpm --filter @tf-lang/trace2tags run build`
   - `pnpm --filter @tf-lang/trace2tags run artifacts`
   - `pnpm --filter @tf-lang/adapter-execution-ts run build`
   - Relevant Vitest suites (`pnpm --filter @tf-lang/utils test`, `pnpm --filter @tf-lang/tf-check test`).

No suitable cherry-pick targets were found in the current tree; implementing the tweaks directly in this branch is the fastest path.
