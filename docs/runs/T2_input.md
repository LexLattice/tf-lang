# T2 — Synthesis Input

| Label | PR | Link | State |
|--:|--:|:--|:-----|
| A | #113 | https://github.com/LexLattice/tf-lang/pull/113 | OPEN |

---

## Run A — PR #113 — Review batch 2 fixes

### PR Body

### Review batch 2 fixes
- DRY: Introduced `@tf-lang/utils` with canonicalJson/paths/tmp/html helpers; all T2 packages use it.
- Paths: artifact/parity scripts auto-detect repo root (no brittle ../../..).
- Security: `coverage.html` escapes tag/spec values (prevents XSS).
- Robustness: parity harness cleans temp dirs even on error.
- Cleanup: removed dead copyCount logic in TS adapter.
- Consistency: aligned @types/node to ^24.3.1 in all new packages.
- CLI: tf-check flag parsing supports --k=v and rejects unknown flags (no new runtime deps).
- Rust bin: `dump` uses `clap` for argument parsing; README returns `Ok(())`.
- Parity: TS↔Rust traces match (`stepIndex`), parity enforced as a hard gate.

------
https://chatgpt.com/codex/tasks/task_e_68c8ee0e66a083209f300d200916121e

### Selected Reviews (codex/gemini)

- **gemini-code-assist** (COMMENTED): ## Summary of Changes

Hello @andreidita22, I'm Gemini Code Assist[^1]! I'm currently reviewing this pull request and will post my feedback shortly. In the meantime, here's a summary to help you and other reviewers quickly get up to speed!

This pull request significantly enhances the codebase by introducing a new shared utility package, `@tf-lang/utils`, which centralizes common functionalities like canonical JSON serialization, repository root detection, and secure HTML escaping. This refactoring improves code reusability and maintainability across various TypeScript packages. Additionally, it bolsters the robustness of parity testing by ensuring proper cleanup of temporary resources, modernizes CLI argument parsing in both TypeScript and Rust components for better usability and error handling, and addresses a potential XSS vulnerability in coverage report generation.

### Highlights

* **New Utility Package**: Introduced `@tf-lang/utils` to centralize common utilities like canonical JSON serialization, repository root detection, temporary directory management, and HTML escaping.
* **Code Reusability (DRY)**: Refactored multiple TypeScript packages (`ts/execution`, `coverage/generator`, `mapper/trace2tags`, `tf-check`) to consume utilities from the new `@tf-lang/utils` package, removing duplicate implementations.
* **Improved Path Handling**: Artifact and parity scripts now robustly auto-detect the repository root using `findRepoRoot` from the new utils package, eliminating brittle relative pathing.
* **Enhanced Security**: The `coverage.html` generation now escapes tag and spec values, mitigating potential Cross-Site Scripting (XSS) vulnerabilities.
* **Robust Parity Testing**: The TypeScript parity harness now ensures temporary directories are cleaned up reliably, even if errors occur during the process, thanks to `withTmpDir`.
* **CLI Argument Parsing**: The `tf-check` CLI now features more flexible argument parsing, supporting `--key=value` syntax and rejecting unknown flags, improving user experience and preventing misconfigurations.
* **Rust CLI Modernization**: The Rust `dump` binary in `tf-adapters-execution` has been updated to use the `clap` crate for robust and user-friendly command-line argument parsing.
* **Dependency Alignment**: Updated `@types/node` to `^24.3.1` across relevant packages for consistency.
* **TS Adapter Cleanup**: Removed unused `copyCount` logic from the TypeScript execution adapter.





<details>
<summary><b>Using Gemini Code Assist</b></summary>
<br>

The full guide for Gemini Code Assist can be found on our [documentation page](https://developers.google.com/gemini-code-assist/docs/review-github-code), here are some quick tips.

<b>Invoking Gemini</b>

You can request assistance from Gemini at any point by creating a comment using either `/gemini <command>` or `@gemini-code-assist <command>`. Below is a summary of the supported commands on the current page.

Feature | Command | Description
--- | --- | ---
Code Review | `/gemini review` | Performs a code review for the current pull request in its current state.
Pull Request Summary | `/gemini summary` | Provides a summary of the current pull request in its current state.
Comment | @gemini-code-assist | Responds in comments when explicitly tagged, both in pull request comments and review comments.
Help | `/gemini help` | Displays a list of available commands.

<b>Customization</b>

To customize Gemini Code Assist for GitHub experience, repository maintainers can create a configuration file and/or provide a custom code review style guide (such as PEP-8 for Python) by creating and adding files to a `.gemini/` folder in the base of the repository. Detailed instructions can be found [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github).

<b>Limitations & Feedback</b>

Gemini Code Assist may make mistakes. Please leave feedback on any instances where its feedback is incorrect or counter productive. You can react with :thumbsup: and :thumbsdown: on @gemini-code-assist comments. If you're interested in giving your feedback about your experience with Gemini Code Assist for Github and other Google products, sign up [here](https://google.qualtrics.com/jfe/form/SV_2cyuGuTWsEw84yG).

<b>You can also get AI-powered code generation, chat, as well as code reviews directly in the IDE at no cost with the [Gemini Code Assist IDE Extension](https://cloud.google.com/products/gemini/code-assist).</b>
</details>




[^1]: Review the [Privacy Notices](https://policies.google.com/privacy), [Generative AI Prohibited Use Policy](https://policies.google.com/terms/generative-ai/use-policy), [Terms of Service](https://policies.google.com/terms), and learn how to configure Gemini Code Assist in GitHub [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github). Gemini can make mistakes, so double check it and [use code with caution](https://support.google.com/legal/answer/13505487).

- **gemini-code-assist** (COMMENTED): ## Code Review

This pull request introduces a significant set of improvements that enhance code quality, robustness, and developer experience. The introduction of the `@tf-lang/utils` package is a great move for DRY principles, centralizing logic for JSON canonicalization, path resolution, and temporary directory management. The security fix to prevent XSS in the coverage report is a critical addition. Furthermore, the CLI enhancements for both the Rust and TS tools make them more robust and user-friendly.

My review includes a few suggestions for further improvement:
- A high-severity fix for a bug in the new CLI argument parser that incorrectly handles empty string values.
- A couple of medium-severity suggestions to adopt more modern and robust JavaScript idioms for object creation and file path handling.

Overall, this is an excellent and well-executed refactoring effort.
- **chatgpt-codex-connector** (COMMENTED): Codex Review: Here are some suggestions.

Reply with `@codex fix comments` to fix any unresolved comments.

<details> <summary>About Codex in GitHub</summary>

[Your team has set up Codex to review pull requests in this repo](http://chatgpt.com/codex/settings/general). Reviews are triggered when you open a pull request for review, mark a draft as ready, or comment "@codex review". If Codex has suggestions, it will comment; otherwise it will react with 👍.

Codex can also answer questions or update the PR. Try commenting "@codex fix this CI failure" or "@codex address that feedback".
</details>

### Selected Review Threads (codex/gemini)

- **Thread** on `packages/tf-check/src/cli.ts` (line 65) (open)
  - **gemini-code-assist**: ![high](https://www.gstatic.com/codereviewagent/high-priority.svg)

The check `if (!value)` on line 63 incorrectly rejects an empty string as a valid value for an option (e.g., `--out ""`). The logic preceding this check already ensures that a value is present if one is required. This check is therefore both redundant and buggy, as it prevents legitimate use cases.
- **Thread** on `packages/utils/src/index.ts` (line 19) (open)
  - **gemini-code-assist**: ![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

This object creation logic can be simplified using `Object.fromEntries()`, which is more concise and idiomatic in modern JavaScript. Additionally, using `localeCompare()` for sorting keys is generally more robust than using `<` and `>` operators, although for typical object keys the difference is often negligible.

```suggestion
    const entries = Object.entries(value as Record<string, unknown>)
      .map(([key, val]) => [key, canonicalize(val)] as const)
      .sort(([left], [right]) => left.localeCompare(right));
    return Object.fromEntries(entries);
```
- **Thread** on `packages/adapters/ts/execution/src/artifacts.ts` (line 10) (open)
  - **gemini-code-assist**: ![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

Using `new URL(...).pathname` to get a directory path from `import.meta.url` can be less robust than the standard library's `fileURLToPath`. The `.pathname` property might not correctly handle all edge cases across different operating systems (e.g., with drive letters on Windows). A safer and more idiomatic approach is to use `fileURLToPath` on a URL object representing the directory. This pattern is used in multiple files (`parity.ts`, `coverage/generator/src/artifacts.ts`, etc.); this comment serves as an example for all of them.

```typescript
const repoRoot = findRepoRoot(fileURLToPath(new URL(".", import.meta.url)));
```
- **Thread** on `packages/tf-check/src/cli.ts` (line 154) (open)
  - **chatgpt-codex-connector**: **[P1] Remove path guard that blocks CLI execution through bin stubs**

The new guard only calls `main()` when `process.argv[1]` resolves to the same path as this module. That works when the file is run directly (`node dist/cli.js`) but fails when the package is executed through its `bin` entry, because Node runs a generated wrapper and *requires* `dist/cli.js` instead. In that common scenario `process.argv[1]` points to the wrapper script, so the condition is false and the CLI exits without running any commands. This effectively breaks `tf-check` for users invoking the published binary. Removing the guard or detecting direct execution via another mechanism (e.g. comparing `import.meta.url` with `process.argv[1]` inside the stub) would restore expected behaviour.

Useful? React with 👍 / 👎.
| B | #114 | https://github.com/LexLattice/tf-lang/pull/114 | OPEN |

---

## Run B — PR #114 — Review batch 2 fixes for T2 tooling

### PR Body

## Summary
- add the new @tf-lang/utils package with shared canonicalization, repo-root discovery, tmpdir cleanup, and HTML escaping helpers and refactor the T2 packages to consume it
- harden tf-check CLI parsing and tests, escape coverage HTML output with a regression test, and drop unused adapter copy bookkeeping
- migrate the Rust dump binary to Clap, update parity to rely on the new flags with guaranteed tmp cleanup, and document the CLI usage

## Testing
- `pnpm -r --filter "./packages/utils" run build`
- `pnpm -r --filter "./packages/tf-lang-l0-ts" run build`
- `pnpm -r --filter @tf-lang/adapter-execution-ts run build`
- `pnpm -r --filter @tf-lang/trace2tags run build`
- `pnpm -r --filter @tf-lang/coverage-generator run build`
- `pnpm -r --filter @tf-lang/tf-check run build`
- `pnpm -r --filter @tf-lang/* run test`
- `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`
- `pnpm --filter @tf-lang/adapter-execution-ts run fixtures` (twice)
- `pnpm --filter @tf-lang/trace2tags run artifacts` (twice)
- `pnpm --filter @tf-lang/coverage-generator run artifacts` (twice)
- `pnpm --filter @tf-lang/tf-check run artifacts` (twice)
- `pnpm --filter @tf-lang/adapter-execution-ts run parity` (twice)

------
https://chatgpt.com/codex/tasks/task_e_68c8ee0e66a083209f300d200916121e

### Selected Reviews (codex/gemini)

- **gemini-code-assist** (COMMENTED): ## Summary of Changes

Hello @andreidita22, I'm Gemini Code Assist[^1]! I'm currently reviewing this pull request and will post my feedback shortly. In the meantime, here's a summary to help you and other reviewers quickly get up to speed!

This pull request focuses on refining and hardening the T2 tooling by centralizing common utility functions into a new shared package, improving the robustness and security of CLI tools, and enhancing the reliability of development processes. Key changes include a new `@tf-lang/utils` package, more resilient CLI argument parsing for `tf-check`, XSS prevention in coverage reports, and a more robust Rust `dump` binary with better temporary file management.

### Highlights

* **New Shared Utilities Package**: Introduced a new `@tf-lang/utils` package containing shared helpers for canonicalization, repository root discovery, temporary directory cleanup, and HTML escaping. All relevant T2 packages now consume these utilities.
* **Hardened tf-check CLI Parsing**: The `tf-check` command-line interface parsing has been made more robust. It now supports `--key=value` flag syntax, rejects unknown flags, and includes regression tests for these improvements.
* **Improved Coverage HTML Security**: The coverage HTML output now properly escapes tag and spec values, preventing potential Cross-Site Scripting (XSS) vulnerabilities. A new regression test ensures this behavior.
* **Rust Dump Binary Migration to Clap**: The Rust `dump` binary has been migrated to use the `clap` crate for argument parsing, improving its CLI interface and robustness. It now uses `--spec` and `--out` flags and guarantees temporary directory cleanup.
* **Enhanced Parity Harness Robustness**: The parity harness now ensures temporary directories are cleaned up reliably, even if errors occur during execution, improving the stability of parity checks.
* **Streamlined Repository Root Detection**: Artifact and parity scripts now automatically detect the repository root, eliminating brittle relative pathing (`../../..`) and improving maintainability.
* **Removed Unused Adapter Logic**: Unused `copyCount` bookkeeping logic has been removed from the TypeScript adapter, simplifying the codebase.
* **Aligned TypeScript Dependencies**: The `@types/node` dependency has been aligned to `^24.3.1` across all new and affected packages for consistency.





<details>
<summary><b>Using Gemini Code Assist</b></summary>
<br>

The full guide for Gemini Code Assist can be found on our [documentation page](https://developers.google.com/gemini-code-assist/docs/review-github-code), here are some quick tips.

<b>Invoking Gemini</b>

You can request assistance from Gemini at any point by creating a comment using either `/gemini <command>` or `@gemini-code-assist <command>`. Below is a summary of the supported commands on the current page.

Feature | Command | Description
--- | --- | ---
Code Review | `/gemini review` | Performs a code review for the current pull request in its current state.
Pull Request Summary | `/gemini summary` | Provides a summary of the current pull request in its current state.
Comment | @gemini-code-assist | Responds in comments when explicitly tagged, both in pull request comments and review comments.
Help | `/gemini help` | Displays a list of available commands.

<b>Customization</b>

To customize Gemini Code Assist for GitHub experience, repository maintainers can create a configuration file and/or provide a custom code review style guide (such as PEP-8 for Python) by creating and adding files to a `.gemini/` folder in the base of the repository. Detailed instructions can be found [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github).

<b>Limitations & Feedback</b>

Gemini Code Assist may make mistakes. Please leave feedback on any instances where its feedback is incorrect or counter productive. You can react with :thumbsup: and :thumbsdown: on @gemini-code-assist comments. If you're interested in giving your feedback about your experience with Gemini Code Assist for Github and other Google products, sign up [here](https://google.qualtrics.com/jfe/form/SV_2cyuGuTWsEw84yG).

<b>You can also get AI-powered code generation, chat, as well as code reviews directly in the IDE at no cost with the [Gemini Code Assist IDE Extension](https://cloud.google.com/products/gemini/code-assist).</b>
</details>




[^1]: Review the [Privacy Notices](https://policies.google.com/privacy), [Generative AI Prohibited Use Policy](https://policies.google.com/terms/generative-ai/use-policy), [Terms of Service](https://policies.google.com/terms), and learn how to configure Gemini Code Assist in GitHub [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github). Gemini can make mistakes, so double check it and [use code with caution](https://support.google.com/legal/answer/13505487).

- **gemini-code-assist** (COMMENTED): ## Code Review

This pull request introduces a significant and high-quality set of improvements across the T2 tooling. The creation of the `@tf-lang/utils` package is a great step towards better code reuse and maintainability, and its application to centralize canonicalization, repository root discovery, and temporary directory handling is well-executed. The hardening of the `tf-check` CLI with a more robust flag parser and the migration of the Rust `dump` binary to Clap are excellent enhancements. Furthermore, the security fix to prevent XSS in the coverage report by escaping HTML is a critical addition, and it's great to see it accompanied by a regression test. Overall, these changes substantially improve the robustness, security, and maintainability of the codebase. I have a couple of minor suggestions in the new `utils` package and the `tf-check` CLI to further enhance code clarity and usability.
- **chatgpt-codex-connector** (COMMENTED): Codex Review: Here are some suggestions.

Reply with `@codex fix comments` to fix any unresolved comments.

<details> <summary>About Codex in GitHub</summary>

[Your team has set up Codex to review pull requests in this repo](http://chatgpt.com/codex/settings/general). Reviews are triggered when you open a pull request for review, mark a draft as ready, or comment "@codex review". If Codex has suggestions, it will comment; otherwise it will react with 👍.

Codex can also answer questions or update the PR. Try commenting "@codex fix this CI failure" or "@codex address that feedback".
</details>

### Selected Review Threads (codex/gemini)

- **Thread** on `packages/utils/src/index.ts` (line 8) (open)
  - **gemini-code-assist**: ![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The `isObject` helper function is functionally correct in its current context because of the preceding `Array.isArray` check in `canonicalize`. However, its implementation (`typeof value === 'object' && value !== null`) is slightly imprecise as it would return `true` for arrays if called directly, and the type guard `value is Record<string, unknown>` would be incorrect in that case. To make this helper more robust and less surprising for future use, I suggest explicitly excluding arrays from the check.

```suggestion
function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
```
- **Thread** on `packages/tf-check/src/cli.ts` (line 58) (open)
  - **gemini-code-assist**: ![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The new `parseFlags` function is a great improvement for making the CLI more robust. However, it doesn't handle common help flags like `--help` or `-h` for subcommands. For example, running `tf-check validate --help` will currently result in an `unknown flag: --help` error. It would be more user-friendly if help flags were supported for subcommands, which would typically display the help text and exit successfully. This could be handled by making `parseFlags` aware of valueless flags like `--help`, or by checking for them in `runCli` before dispatching to subcommand handlers.
- **Thread** on `packages/tf-check/src/artifacts.ts` (line 9) (open)
  - **chatgpt-codex-connector**: **[P1] Pass decoded filesystem path to findRepoRoot**

The new artifact script calls `findRepoRoot(new URL(".", import.meta.url).pathname)`, but `URL.pathname` retains percent‑encoded characters. When the repository lives in a directory whose name contains spaces or other characters that require encoding (e.g. `~/TF Lang/`), this expression resolves to `/~/TF%20Lang/...`, which does not exist on disk. `findRepoRoot` then walks upward from `/` and throws `repository root not found`, causing the CLI to fail before writing artifacts. Use `fileURLToPath(new URL('.', import.meta.url))` or reuse the already decoded `here` variable instead. The same issue is present in the other artifact and parity helpers added in this commit.

Useful? React with 👍 / 👎.
| C | #115 | https://github.com/LexLattice/tf-lang/pull/115 | OPEN |

---

## Run C — PR #115 — T2: review batch 2 fixes

### PR Body

## Summary
- add @tf-lang/utils package with shared canonicalization, repo root detection, tmp dir, and HTML escaping helpers and rewire the T2 packages to consume it
- harden coverage output and parity harness (HTML escaping, repo root lookup, Clap flags) plus remove unused adapter copy counter
- tighten tf-check CLI flag parsing, align @types/node to ^24.3.1, and migrate the Rust dump binary + docs to Clap

## Testing
- pnpm -r --filter "./packages/utils" run build
- pnpm -r --filter "./packages/tf-lang-l0-ts" run build
- pnpm -r --filter @tf-lang/adapter-execution-ts run build
- pnpm -r --filter @tf-lang/trace2tags run build
- pnpm -r --filter @tf-lang/coverage-generator run build
- pnpm -r --filter @tf-lang/tf-check run build
- pnpm -r --filter @tf-lang/* run test
- cargo test --workspace --all-targets --manifest-path crates/Cargo.toml
- pnpm --filter @tf-lang/adapter-execution-ts run fixtures
- pnpm --filter @tf-lang/trace2tags run artifacts
- pnpm --filter @tf-lang/coverage-generator run artifacts
- pnpm --filter @tf-lang/tf-check run artifacts
- pnpm --filter @tf-lang/adapter-execution-ts run parity

------
https://chatgpt.com/codex/tasks/task_e_68c8ee0e66a083209f300d200916121e

### Selected Reviews (codex/gemini)

- **gemini-code-assist** (COMMENTED): ## Summary of Changes

Hello @andreidita22, I'm Gemini Code Assist[^1]! I'm currently reviewing this pull request and will post my feedback shortly. In the meantime, here's a summary to help you and other reviewers quickly get up to speed!

This pull request focuses on a second batch of review fixes aimed at improving the overall quality, security, and maintainability of the codebase. Key changes include the introduction of a shared utilities package to centralize common functions, hardening of existing tools against potential vulnerabilities and errors, and refining command-line interfaces for better usability. These updates contribute to a more robust and consistent development ecosystem.

### Highlights

* **New Shared Utilities Package**: Introduced a new `@tf-lang/utils` package to centralize common functionalities such as canonical JSON serialization, repository root detection, temporary directory management, and HTML escaping. This promotes code reuse and consistency across the project.
* **Enhanced Coverage Report Security**: Implemented HTML escaping for user-provided tag and spec values within the `coverage.html` output, effectively mitigating potential Cross-Site Scripting (XSS) vulnerabilities.
* **Improved Parity Harness Robustness**: The parity harness now automatically cleans up temporary directories, even in cases of errors, ensuring a cleaner and more reliable testing environment. It also leverages the new repository root detection utility.
* **Refined `tf-check` CLI Argument Parsing**: The `tf-check` command-line interface has been hardened to support `--flag=value` syntax, correctly parse arguments, and explicitly reject unknown or missing flags, leading to a more predictable and user-friendly CLI experience.
* **Rust `dump` Binary Migration to Clap**: The Rust `dump` binary has been updated to utilize the `clap` crate for command-line argument parsing, replacing manual `env::args()` handling. This provides a more robust and feature-rich argument parsing solution for the Rust toolchain.
* **Standardized Node.js Type Definitions**: The `@types/node` dependency has been aligned to `^24.3.1` across all relevant TypeScript packages, ensuring consistent type definitions and reducing potential compatibility issues.
* **Cleanup of Unused Adapter Logic**: Removed the `copyCount` logic from the TypeScript adapter, as it was no longer in use, contributing to a leaner and more maintainable codebase.





<details>
<summary><b>Using Gemini Code Assist</b></summary>
<br>

The full guide for Gemini Code Assist can be found on our [documentation page](https://developers.google.com/gemini-code-assist/docs/review-github-code), here are some quick tips.

<b>Invoking Gemini</b>

You can request assistance from Gemini at any point by creating a comment using either `/gemini <command>` or `@gemini-code-assist <command>`. Below is a summary of the supported commands on the current page.

Feature | Command | Description
--- | --- | ---
Code Review | `/gemini review` | Performs a code review for the current pull request in its current state.
Pull Request Summary | `/gemini summary` | Provides a summary of the current pull request in its current state.
Comment | @gemini-code-assist | Responds in comments when explicitly tagged, both in pull request comments and review comments.
Help | `/gemini help` | Displays a list of available commands.

<b>Customization</b>

To customize Gemini Code Assist for GitHub experience, repository maintainers can create a configuration file and/or provide a custom code review style guide (such as PEP-8 for Python) by creating and adding files to a `.gemini/` folder in the base of the repository. Detailed instructions can be found [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github).

<b>Limitations & Feedback</b>

Gemini Code Assist may make mistakes. Please leave feedback on any instances where its feedback is incorrect or counter productive. You can react with :thumbsup: and :thumbsdown: on @gemini-code-assist comments. If you're interested in giving your feedback about your experience with Gemini Code Assist for Github and other Google products, sign up [here](https://google.qualtrics.com/jfe/form/SV_2cyuGuTWsEw84yG).

<b>You can also get AI-powered code generation, chat, as well as code reviews directly in the IDE at no cost with the [Gemini Code Assist IDE Extension](https://cloud.google.com/products/gemini/code-assist).</b>
</details>




[^1]: Review the [Privacy Notices](https://policies.google.com/privacy), [Generative AI Prohibited Use Policy](https://policies.google.com/terms/generative-ai/use-policy), [Terms of Service](https://policies.google.com/terms), and learn how to configure Gemini Code Assist in GitHub [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github). Gemini can make mistakes, so double check it and [use code with caution](https://support.google.com/legal/answer/13505487).

- **gemini-code-assist** (COMMENTED): ## Code Review

This pull request introduces a significant refactoring by creating a shared `@tf-lang/utils` package to centralize common helpers like JSON canonicalization, path resolution, and temporary directory management. This DRYs up the codebase across several packages. The changes also harden the tooling, with the Rust `dump` binary migrating to `clap` for more robust argument parsing, and the `tf-check` TypeScript CLI receiving a stricter flag parser. Security is improved by escaping HTML in the coverage report to prevent XSS vulnerabilities. Overall, these are excellent improvements for maintainability, robustness, and security. I have one suggestion to improve consistency in path resolution within the `tf-check` CLI.

### Selected Review Threads (codex/gemini)

- **Thread** on `packages/tf-check/src/cli.ts` (line 101) (open)
  - **gemini-code-assist**: ![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The default output directory for the `artifacts` command is resolved relative to the current working directory using `path.resolve()`. This is inconsistent with other artifact-generating scripts in this PR (e.g., in `adapter-execution-ts`, `coverage-generator`) which now use `findRepoRoot()` to ensure artifacts are always placed relative to the repository root. This makes the tool's behavior dependent on where it's run from.

To improve consistency and robustness, consider using `findRepoRoot()` here as well. You will need to import `findRepoRoot` from `@tf-lang/utils`.

```suggestion
    const outDir = outDirValue ?? path.join(findRepoRoot(), "out/t2/tf-check");
```
| D | #116 | https://github.com/LexLattice/tf-lang/pull/116 | OPEN |

---

## Run D — PR #116 — Review batch 2 fixes

### PR Body

### Review batch 2 fixes
- DRY: Introduced `@tf-lang/utils` with canonicalJson/paths/tmp/html helpers; all T2 packages use it.
- Paths: artifact/parity scripts auto-detect repo root (no brittle ../../..).
- Security: `coverage.html` escapes tag/spec values (prevents XSS).
- Robustness: parity harness cleans temp dirs even on error.
- Cleanup: removed dead copyCount logic in TS adapter.
- Consistency: aligned @types/node to ^24.3.1 in all new packages.
- CLI: tf-check flag parsing supports --k=v and rejects unknown flags (no new runtime deps).
- Rust bin: `dump` uses `clap` for argument parsing; README returns `Ok(())`.
- Parity: TS↔Rust traces match (`stepIndex`), parity enforced as a hard gate.


------
https://chatgpt.com/codex/tasks/task_e_68c8ee0e66a083209f300d200916121e

### Selected Reviews (codex/gemini)

- **gemini-code-assist** (COMMENTED): ## Summary of Changes

Hello @andreidita22, I'm Gemini Code Assist[^1]! I'm currently reviewing this pull request and will post my feedback shortly. In the meantime, here's a summary to help you and other reviewers quickly get up to speed!

This pull request significantly refactors and improves the project's codebase by introducing a new shared utility package, centralizing common functionalities and reducing code duplication. It also enhances the overall stability and security of the system through more robust path handling, secure HTML output, and reliable temporary file management. Furthermore, the command-line interfaces for both TypeScript and Rust tools have been made more user-friendly and resilient to incorrect inputs, and the consistency between trace generation across languages has been verified.

### Highlights

* **New Shared Utility Package**: Introduced `@tf-lang/utils` to centralize common helpers for canonical JSON serialization, repository root detection, temporary directory management, and HTML escaping, promoting code reusability across all T2 packages.
* **Enhanced Robustness and Security**: Improved artifact and parity scripts with auto-detection of the repository root, preventing brittle relative path issues. Implemented XSS prevention in `coverage.html` by escaping tag and spec values, and ensured parity harness cleans temporary directories even on errors.
* **Refined CLI Argument Parsing**: The `tf-check` CLI now supports `--key=value` syntax for flags and rejects unknown flags, enhancing user experience and preventing misconfigurations. The Rust `dump` binary also adopted `clap` for robust argument parsing.
* **Code Cleanup and Consistency**: Removed dead `copyCount` logic from the TypeScript adapter and aligned `@types/node` to `^24.3.1` across all new packages for dependency consistency.
* **Strengthened Parity Checks**: Ensured that TypeScript and Rust traces match, specifically for `stepIndex`, and enforced parity as a hard gate in the development process.





<details>
<summary><b>Using Gemini Code Assist</b></summary>
<br>

The full guide for Gemini Code Assist can be found on our [documentation page](https://developers.google.com/gemini-code-assist/docs/review-github-code), here are some quick tips.

<b>Invoking Gemini</b>

You can request assistance from Gemini at any point by creating a comment using either `/gemini <command>` or `@gemini-code-assist <command>`. Below is a summary of the supported commands on the current page.

Feature | Command | Description
--- | --- | ---
Code Review | `/gemini review` | Performs a code review for the current pull request in its current state.
Pull Request Summary | `/gemini summary` | Provides a summary of the current pull request in its current state.
Comment | @gemini-code-assist | Responds in comments when explicitly tagged, both in pull request comments and review comments.
Help | `/gemini help` | Displays a list of available commands.

<b>Customization</b>

To customize Gemini Code Assist for GitHub experience, repository maintainers can create a configuration file and/or provide a custom code review style guide (such as PEP-8 for Python) by creating and adding files to a `.gemini/` folder in the base of the repository. Detailed instructions can be found [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github).

<b>Limitations & Feedback</b>

Gemini Code Assist may make mistakes. Please leave feedback on any instances where its feedback is incorrect or counter productive. You can react with :thumbsup: and :thumbsdown: on @gemini-code-assist comments. If you're interested in giving your feedback about your experience with Gemini Code Assist for Github and other Google products, sign up [here](https://google.qualtrics.com/jfe/form/SV_2cyuGuTWsEw84yG).

<b>You can also get AI-powered code generation, chat, as well as code reviews directly in the IDE at no cost with the [Gemini Code Assist IDE Extension](https://cloud.google.com/products/gemini/code-assist).</b>
</details>




[^1]: Review the [Privacy Notices](https://policies.google.com/privacy), [Generative AI Prohibited Use Policy](https://policies.google.com/terms/generative-ai/use-policy), [Terms of Service](https://policies.google.com/terms), and learn how to configure Gemini Code Assist in GitHub [here](https://developers.google.com/gemini-code-assist/docs/customize-gemini-behavior-github). Gemini can make mistakes, so double check it and [use code with caution](https://support.google.com/legal/answer/13505487).

- **gemini-code-assist** (COMMENTED): ## Code Review

This is an excellent pull request that significantly improves the codebase by introducing a shared `@tf-lang/utils` package, which greatly reduces code duplication. The changes enhance robustness, security, and consistency across the board. Key improvements include hardening the coverage report against XSS vulnerabilities, making path resolution more reliable by detecting the repository root, improving CLI argument parsing, and ensuring temporary directories are cleaned up reliably. The migration of the Rust `dump` binary to `clap` is also a great enhancement for usability. I have a couple of minor suggestions in the new `utils` package to further improve security hardening and code conciseness.

### Selected Review Threads (codex/gemini)

- **Thread** on `packages/utils/src/index.ts` (line 19) (open)
  - **gemini-code-assist**: ![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

This `for...of` loop to construct the object can be simplified using `Object.fromEntries()`. This is a more modern and concise way to convert a list of key-value pairs back into an object, which can improve readability.

```suggestion
    return Object.fromEntries(entries);
```
- **Thread** on `packages/utils/src/index.ts` (line 65) (open)
  - **gemini-code-assist**: ![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

For improved security hardening against XSS, it's a good practice to also escape the forward slash (`/`) character. This helps prevent scenarios where user-provided input could prematurely close an HTML tag, such as in `<script src="..."></script>`. While the current implementation is safe for the places it's used, adding this provides an extra layer of defense-in-depth.

```suggestion
const HTML_ESCAPE_MAP: Record<string, string> = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': "&quot;",
  "'": "&#39;",
  "/": "&#x2F;",
};

const HTML_ESCAPE_REGEX = /[&<>"'/]/g;
```
