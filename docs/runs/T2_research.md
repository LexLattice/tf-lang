# T2 Research Notes — CLI, Paths, Utils

## Scope
Requested follow-up review of items raised across PRs #113–#116. For each, I checked whether the change already exists on this branch, whether there is an alternate PR to cherry-pick from, and the best implementation path if missing. Tests/builds run earlier in this session are noted where relevant.

---

## 1. CLI: correctness & UX

| Item | Status in current branch | Alternate PR? | Recommendation |
| --- | --- | --- | --- |
| Allow empty string option values in tf-check CLI | **Done.** Parser accepts `--out=""` and positional empty strings; new tests cover both syntaxes (`packages/tf-check/tests/validator.test.ts:76`). | n/a | No action needed. |
| Remove/bypass direct-execution guard | **Done previously.** `main()` runs unconditionally (`packages/tf-check/src/cli.ts:158`). | n/a | — |
| Support `-h/--help` when passed to subcommands | **Done.** Parser now tracks toggle flags per subcommand, prints scoped usage, and tests assert behaviour (`packages/tf-check/tests/validator.test.ts:86`). | n/a | — |

Tests: `pnpm --filter @tf-lang/tf-check run build` executed successfully after earlier fixes; once parser is updated, rerun the same command plus targeted Vitest suites.

---

## 2. Paths & repo-root resolution

| Item | Status | Alternate PR? | Recommendation |
| --- | --- | --- | --- |
| Replace `URL.pathname` with `fileURLToPath` | **Done.** Remaining helpers (parity, legal examples) now decode URLs, and CI will fail if new `.pathname` usages slip in. | n/a | — |
| Anchor tf-check artifacts dir to repo root | **Done.** CLI resolves the repo root lazily with a cached fallback to `out/t2/tf-check` when no workspace is found (`packages/tf-check/src/cli.ts:25`). | n/a | — |

Tests: We’ve run `pnpm --filter @tf-lang/trace2tags run artifacts` and `pnpm --filter @tf-lang/adapter-execution-ts run build`; after the path fixes, rerun those commands to confirm the repo-root lookups still succeed.

---

## 3. `@tf-lang/utils`

| Item | Status | Alternate PR? | Recommendation |
| --- | --- | --- | --- |
| Use `Object.fromEntries` in `canonicalize` | **Done.** Canonicalization now rebuilds objects via `Object.fromEntries` and ASCII sorts keys for determinism (`packages/utils/src/index.ts:12`). | n/a | — |
| Harden `isObject` guard | **Done.** Added `isPlainObject` to bypass arrays and nulls (`packages/utils/src/index.ts:20`). | n/a | — |
| Escape `/` in `escapeHtml` | **Done.** Added to the escape map/regex with tests (`packages/utils/src/index.ts:57`, `packages/utils/tests/index.test.ts:23`). | n/a | — |

Tests: `pnpm --filter @tf-lang/trace2tags run build` and `pnpm --filter @tf-lang/tf-check run build` already exercise canonicalization/escaping; focused unit tests now cover empty flag values, help toggles, ASCII ordering, and HTML escaping.

---

## 4. Tests & parity gates

- XSS regression: the existing coverage generator tests still pass (`pnpm --filter @tf-lang/trace2tags run artifacts` depends on the HTML generation). No changes needed besides maintaining coverage once `/` escaping is added.
- CLI parser tests: add cases for `--out=""`, `--help` on subcommands, and unknown short flags. Existing Vitest targets should catch regressions.
- Repo-root discovery: after replacing `.pathname`, consider adding a unit test or integration test that stubs a path with spaces to ensure `findRepoRoot` handling remains correct (manual testing on the Windows runner is still advisable).
- Parity tmp cleanup: logic already lives in utils (`withTmpDir`) and parity harness; current parity build succeeded, so no additional action unless new changes affect it.

---

## 5. Tiny polish checklist (T2)

- **Bin smoke**: Added CI step to pack/install `tf-check` and run `--help`; ensures published bin stays functional.
- **Fallback test**: `resolveDefaultArtifactsDir` accepts an injectable resolver and exposes a test reset hook; unit test verifies the fallback when `findRepoRoot` throws (`packages/tf-check/tests/validator.test.ts:96`).
- **Flags policy**: HELP text documents that combined short flags aren’t supported; tests confirm `-hv` errors.
- **Deterministic sort**: Canonicalization uses ASCII comparison to avoid locale drift; test asserts ordering of mixed-case keys (`packages/utils/tests/index.test.ts:31`).
- **No `.pathname` rule**: Workflow now fails if new helpers rely on `new URL(..., import.meta.url).pathname`; remaining usages converted to `fileURLToPath`.

---

## Summary / Next Steps

All checklist items are complete. Rerun the CI surface (`pnpm --filter @tf-lang/tf-check run build`, `pnpm --filter @tf-lang/tf-check test`, `pnpm --filter @tf-lang/adapter-execution-ts run build`, `pnpm --filter @tf-lang/trace2tags run artifacts`, `pnpm --filter @tf-lang/utils test`) whenever related files change to ensure regressions are caught early.
