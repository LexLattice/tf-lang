# Track H: Prover Deepening

## What exists now

*   **Laws CLI**: A `tf laws` command is implemented in `tools/tf-lang-cli/index.mjs`. It can check a specific goal (e.g., `--goal branch-exclusive`) against an L0 file.
*   **Branch Exclusivity Prover**: The `branch_exclusive` goal is backed by a Z3 prover integration (`packages/prover/z3.mjs` and `laws/branch_exclusive.mjs`). It can formally prove whether two branches guarded by a boolean variable are mutually exclusive.
*   **Counterexamples**: When a proof fails, the `tf laws` command provides a minimal counterexample. For `branch-exclusive`, it shows the variable assignment that causes the overlap (e.g., `decision=true`) and lists the nodes in each branch that are active simultaneously.
*   **Other Law Checks**: The system includes stubs for checking `monotonic_log` and `confidential_envelope`, which currently perform simple pattern matching rather than formal verification. For example, `monotonic_log` passes if it finds a publish to `policy:record`, and `confidential_envelope` passes if it finds a publish to `policy:secure`.

## How to run

*   **Check laws for an L0 file**:
    ```bash
    node tools/tf-lang-cli/index.mjs laws --check <L0_FILE> --goal <GOAL>
    ```

*   **Example: Check branch exclusivity on a valid file**:
    ```bash
    node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive
    ```
    *Output*: `status: GREEN`, `branch_exclusive: PASS`

*   **Example: Check branch exclusivity on a file with an overlap**:
    ```bash
    # Using a test file where both branches use 'when: "@decision"'
    node tools/tf-lang-cli/index.mjs laws --check out/0.6/review/H/fail_test/fail.l0.json --goal branch-exclusive
    ```
    *Output*: `status: RED`, `branch_exclusive: RED`, and a `Counterexample` section explaining the failure.

## Common errors + fixes

*   **Error**: `status: RED` with `reason: overlap` and a counterexample.
    *   **Cause**: The `when` conditions for two branches are not mutually exclusive. For example, both might be active when a variable is `true`.
    *   **Fix**: Correct the logic in the L2 pipeline's `branch` step to ensure the `when` conditions are logically opposite (e.g., `@decision` and `!(@decision)`).

*   **Error**: `branch_exclusive: WARN` with `reason: unsupported-guard`.
    *   **Cause**: The `when` condition is too complex for the prover to analyze (e.g., it involves multiple variables or complex expressions).
    *   **Fix**: Refactor the L2 pipeline to use a single boolean variable for the branch condition. The complex logic should be moved into a `Transform` node that produces this boolean variable.

## Gaps

1.  **DX (Opaque Prover)**: The Z3 prover is a critical component, but it's treated like a black box. There is no documentation on how it's invoked, what SMT-LIB code is generated, or how to debug it. The error `solver-failed` provides no actionable information.
2.  **Incompleteness (Shallow Law Checks)**: The `monotonic_log` and `confidential_envelope` checks are shallow pattern matches, not deep proofs. They check for the *presence* of a certain publish event but don't verify the *content* or *logic* (e.g., that the log is actually append-only, or that plaintext is never exposed alongside ciphertext). This provides a false sense of security.
3.  **Documentation (Goals)**: The `tf laws` command requires a `--goal` argument, but there is no way to list the available goals. A user must find them by reading the source code or documentation.
4.  **DX (Noisy Counterexamples)**: The counterexample format is useful but could be improved. It doesn't explicitly state which L0 nodes are in conflict, instead listing all nodes in the positive and negative paths, which can be verbose.

## Next 3 improvements

1.  **Deepen the `monotonic_log` and `confidential_envelope` provers.**
    *   **Action**: Enhance these law checkers to perform more meaningful verification. `monotonic_log` should check that the log's key is derived from a monotonically increasing value (like a timestamp or version). `confidential_envelope` should check that if a payload contains ciphertext, it does not also contain the corresponding plaintext.
    *   **Impact**: Critical. Fulfills the promise of "Prover Deepening" and closes major security/correctness gaps.
    *   **Effort**: Large.

2.  **Add introspection and debugging to the Z3 prover harness.**
    *   **Action**: Add a `--debug-prover` flag to `tf laws`. When enabled, it should dump the generated SMT-LIB script to a file and log the raw output from the Z3 solver. This would allow developers to debug solver issues.
    *   **Impact**: High. Makes the most advanced part of the system maintainable and extensible.
    *   **Effort**: Medium.

3.  **Improve the `tf laws` CLI experience.**
    *   **Action**:
        1.  Add a `tf laws --list-goals` command.
        2.  Refine the counterexample output to pinpoint the exact nodes that are in conflict.
    *   **Impact**: High. Improves the discoverability and usability of the laws CLI.
    *   **Effort**: Medium.