# Authoring TF-Lang Laws

The law system keeps the checker, prover harness, and documentation in lockstep. Use this guide when you add a new goal or extend an existing checker.

## 1. Discover the current surface area

* List the canonical goal identifiers along with human-readable descriptions:

  ```bash
  pnpm tf laws --list-goals
  ```
* Each goal maps to an entry in `packages/checker/law-goals.mjs`. Extend that list when you introduce a new goal so both the checker and CLI stay in sync.
* Existing implementations live under `laws/*.mjs` and are wired into the checker via `packages/checker/check.mjs`.

## 2. Thread metadata through expansion

* L1/L0 expansion must tag any nodes that participate in a law with metadata the checker can read. For example, `state.merge` emits `meta.law = { goal: 'state-merge', strategy: 'crdt.gcounter' }` so the checker can validate the configured merge strategy.
* Prefer attaching stable identifiers (node IDs, channel names, guard variables) because they flow into the evidence bundle the CLI prints.

## 3. Emit structured evidence

* Law modules return `{ goal, ok, results, evidence }` objects. Each `result` should carry the node ID (or branch label) plus any domain-specific context (`issues`, `assumption`, `plaintextPaths`, etc.).
* When a proof involves the SMT solver, return the generated SMT-LIB text. The checker writes it to `out/laws/<pipeline-id>/<goal>.smt2` so the CLI can show the file when `--verbose` is set.
* On solver failures, attach a JSON-friendly `error` object with the captured flags and root cause so downstream tooling can triage without inspecting stack traces.

## 4. Tighten the checker

* Update `packages/checker/check.mjs` to import the new law, call it from `runChecks`, and merge the result with goal metadata via `withGoalMetadata`.
* Extend the overall `overallGreen` logic only when the new law should influence release gating.
* Add a targeted test in `tests/checker/` to cover pass, warn, and fail scenarios, mirroring how existing law tests are structured.

## 5. Extend the CLI

* Print all registered goals and surface evidence paths when verbose mode is active:

  ```bash
  pnpm tf laws --check <file.l0.json> [--goal <id>] [--verbose]
  ```
* Update `tools/tf-lang-cli/tests/` to cover any new command line permutations or JSON output changes.

## 6. Document the workflow

* Reference new goals from `out/0.6/review/_proposals/*.md` and the v0.6 enhancement plan so the progress matrix remains accurate.
* When in doubt, mirror the patterns used by `branch-exclusive`, `idempotency`, and `confidential-envelope`—they cover solver integration, state metadata, and content inspection respectively.

Following these steps keeps the law/prover surface transparent and reproducible for both the CLI and release tooling.
