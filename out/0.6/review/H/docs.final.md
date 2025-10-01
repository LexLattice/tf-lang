# Track H · Prover deepening

## What exists now
- **Laws CLI**: A `tf laws` command is implemented in `tools/tf-lang-cli/index.mjs`. It can check a specific goal (e.g., `--goal branch-exclusive`) against an L0 file.
- **Branch Exclusivity Prover**: The `branch_exclusive` goal is backed by a Z3 prover integration (`packages/prover/z3.mjs` and `laws/branch_exclusive.mjs`). It can formally prove whether two branches guarded by a boolean variable are mutually exclusive.
- **Counterexamples**: When a proof fails, the `tf laws` command provides a minimal counterexample. For `branch-exclusive`, it shows the variable assignment that causes the overlap (e.g., `decision=true`) and lists the nodes in each branch that are active simultaneously.
- **Other Law Checks**: The system includes stubs for checking `monotonic_log` and `confidential_envelope`, which currently perform simple pattern matching rather than formal verification. For example, `monotonic_log` passes if it finds a publish to `policy:record`, and `confidential_envelope` passes if it finds a publish to `policy:secure`.
- **Solver bindings** (`packages/prover/z3.mjs`): lazy-loads `z3-solver` and exposes `proveStableCorrImpliesIdempotent` + `proveGuardExclusive` helpers.
- **Counterexample finder** (`packages/prover/counterexample.mjs`): enumerates boolean assignments (≤8 vars) and reports triggered rule IDs for branch overlaps or max-bound exceedance.
- **Law suite integration** (`laws/*.mjs`): idempotency uses Z3 implication proof; branch exclusivity funnels through prover guards; monotonic log + confidential envelope report PASS/WARN heuristics.
- **CLI access**: `tf laws --check` surfaces branch exclusivity/monotonic/confidential results with `--max-bools` and optional JSON output.

## How to run (10-minute quickstart)
1. **Check laws for an L0 file**.
```bash
node tools/tf-lang-cli/index.mjs laws --check <L0_FILE> --goal <GOAL>
```
2. **Example: Check branch exclusivity on a valid file**.
```bash
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive
```
3. **Example: Check branch exclusivity on a file with an overlap**.
```bash
node tools/tf-lang-cli/index.mjs laws --check out/0.6/review/H/fail_test/fail.l0.json --goal branch-exclusive
```
4. *Output*: status: RED, `branch_exclusive: RED`, and a `Counterexample` section explaining the failure.
```bash
status: RED
```
5. Run command.
```bash
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive --max-bools 4
```
```bash
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive --json
```
6. Inspect output for WARN (e.g., confidential envelope plaintext) or `max-bools-exceeded` sentinel when guard space too large.
```bash
WARN
```

## Common errors & fixes
| Symptom | Probable cause | Fix |
| --- | --- | --- |
| `status: RED` with `reason: overlap` and a counterexample. | The `when` conditions for two branches are not mutually exclusive. For example, both might be active when a variable is `true`. | Correct the logic in the L2 pipeline's `branch` step to ensure the `when` conditions are logically opposite (e.g., `@decision` and `!(@decision)`). |
| `branch_exclusive: WARN` with `reason: unsupported-guard`. | The `when` condition is too complex for the prover to analyze (e.g., it involves multiple variables or complex expressions). | Refactor the L2 pipeline to use a single boolean variable for the branch condition. The complex logic should be moved into a `Transform` node that produces this boolean variable. |
| `solver-init-missing` arises when `z3-solver` optional dep is not installed; rerun `pnpm install --frozen-lockfile` and ensure Node 20. | Investigate root cause | Document mitigation |
| Large guard sets trigger `max-bools-exceeded`; lower branching by splitting conditionals or increase bound (capped at 8). | Investigate root cause | Document mitigation |
| `predicate-required` from `findCounterexample` indicates a law handler invoked prover without predicate; file an issue—the CLI should never expose it. | Investigate root cause | Document mitigation |

## Acceptance gates & signals
| Gate | Command | Success signal |
| --- | --- | --- |
| **Check laws for an L0 file** | `node tools/tf-lang-cli/index.mjs laws --check <L0_FILE> --goal <GOAL>` | Command succeeds without errors. |
| **Example: Check branch exclusivity on a valid file** | `node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive` | Command succeeds without errors. |
| **Example: Check branch exclusivity on a file with an overlap** | `node tools/tf-lang-cli/index.mjs laws --check out/0.6/review/H/fail_test/fail.l0.json --goal branch-exclusive` | Command succeeds without errors. |
| *Output*: status: RED, `branch_exclusive: RED`, and a `Counterexample` section explaining the failure | `status: RED` | Command succeeds without errors. |
| Run command | `node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive --max-bools 4` | Command succeeds without errors. |
| Run command | `node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive --json` | Command succeeds without errors. |
| Inspect output for WARN (e.g., confidential envelope plaintext) or `max-bools-exceeded` sentinel when guard space too large | `WARN` | Command succeeds without errors. |

## DX gaps
- **DX (Opaque Prover)**: The Z3 prover is a critical component, but it's treated like a black box. There is no documentation on how it's invoked, what SMT-LIB code is generated, or how to debug it. The error `solver-failed` provides no actionable information.
- **Incompleteness (Shallow Law Checks)**: The `monotonic_log` and `confidential_envelope` checks are shallow pattern matches, not deep proofs. They check for the *presence* of a certain publish event but don't verify the *content* or *logic* (e.g., that the log is actually append-only, or that plaintext is never exposed alongside ciphertext). This provides a false sense of security.
- **Documentation (Goals)**: The `tf laws` command requires a `--goal` argument, but there is no way to list the available goals. A user must find them by reading the source code or documentation.
- **DX (Noisy Counterexamples)**: The counterexample format is useful but could be improved. It doesn't explicitly state which L0 nodes are in conflict, instead listing all nodes in the positive and negative paths, which can be verbose.
- No CLI exposes counterexample JSON directly; branch exclusivity NEUTRAL gives no insight into guard coverage.
- Confidential envelope + monotonic log rely on heuristics, not solver-backed proofs; WARNs never fail builds, weakening compliance story.
- No docs describing how to author custom law goals or interpret prover payloads.

## Top issues (synthesized)
- **DX (Opaque Prover)**: The Z3 prover is a critical component, but it's treated like a black box. There is no documentation on how it's invoked, what SMT-LIB code is generated, or how to debug it. The error `solver-failed` provides no actionable information.
- **Incompleteness (Shallow Law Checks)**: The `monotonic_log` and `confidential_envelope` checks are shallow pattern matches, not deep proofs. They check for the *presence* of a certain publish event but don't verify the *content* or *logic* (e.g., that the log is actually append-only, or that plaintext is never exposed alongside ciphertext). This provides a false sense of security.
- **Documentation (Goals)**: The `tf laws` command requires a `--goal` argument, but there is no way to list the available goals. A user must find them by reading the source code or documentation.

## Next 3 improvements
- **Deepen the `monotonic_log` and `confidential_envelope` provers** — Action: Enhance these law checkers to perform more meaningful verification. `monotonic_log` should check that the log's key is derived from a monotonically increasing value (like a timestamp or version). `confidential_envelope` should check that if a payload contains ciphertext, it does not also contain the corresponding plaintext; Impact: Critical. Fulfills the promise of "Prover Deepening" and closes major security/correctness gaps; Effort: Large
- **Add introspection and debugging to the Z3 prover harness** — Action: Add a `--debug-prover` flag to `tf laws`. When enabled, it should dump the generated SMT-LIB script to a file and log the raw output from the Z3 solver. This would allow developers to debug solver issues; Impact: High. Makes the most advanced part of the system maintainable and extensible; Effort: Medium
- **Improve the `tf laws` CLI experience** — Action: Add a `tf laws --list-goals` command. Refine the counterexample output to pinpoint the exact nodes that are in conflict; Impact: High. Improves the discoverability and usability of the laws CLI; Effort: Medium

## References
- [tools/tf-lang-cli/index.mjs](../../../../tools/tf-lang-cli/index.mjs)
- [packages/prover/z3.mjs](../../../../packages/prover/z3.mjs)
- [laws/branch_exclusive.mjs](../../../../laws/branch_exclusive.mjs)
- [examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json](../../../../examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json)
- [packages/prover/counterexample.mjs](../../../../packages/prover/counterexample.mjs)
