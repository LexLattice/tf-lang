# Track C: Runtime & Checker

## What exists now

*   **Runtime / Executor**: An L0 DAG executor is implemented in `packages/runtime/run.mjs`. It processes an L0 file's `nodes` array, simulates `Publish` and `Subscribe` events using an in-memory message bus (`bus.memory.mjs`), and executes `Transform` and `Keypair` primitives. It can be seeded with initial events and supports custom handlers for specific channels.
*   **Checker**: The core checker (`packages/checker/check.mjs`) is a comprehensive static analysis tool. It verifies:
    *   **Effects**: Compares declared vs. computed effects (`Outbound`, `Inbound`, `Entropy`, `Pure`).
    *   **Policy**: Ensures all `Publish`/`Subscribe` channels are in a configurable allow-list (`policy/policy.allow.json`).
    *   **Capabilities**: Matches required capabilities (e.g., `cap:publish:rpc:req:*`) against a provided list, using a lattice (`policy/capability.lattice.json`) to derive requirements.
    *   **Laws**: Orchestrates checks for algebraic laws (idempotency, CRDT properties) and logical properties (RPC pairing, branch exclusivity).
*   **Z3 Harness**: The checker integrates with the Z3 prover via modules in the `laws/` directory. For example, `laws/branch_exclusive.mjs` parses `when` clauses, identifies branches, and calls the Z3 harness (`packages/prover/z3.mjs`) to prove that positive and negative branches are mutually exclusive.

## How to run

*   **Run the Checker on an L0 file**:
    ```bash
    node packages/checker/check.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --out out/0.6/review/C/TFREPORT.json
    ```
    This command runs all checks and writes a detailed JSON report to the specified output file.

*   **Run the L0 Executor (Runtime)**:
    The runtime is a library function (`executeL0`) and not exposed directly as a CLI command. It is used in tests and other scripts. A conceptual example:
    ```javascript
    // import { executeL0 } from 'packages/runtime/run.mjs';
    // const l0 = JSON.parse(fs.readFileSync('...'));
    // const { trace } = await executeL0(l0);
    ```

## Common errors + fixes

*   **Error**: `Checker reports status: RED`
    *   **Cause**: One or more checks failed (e.g., an effect was missing, a channel was not in the policy, or a law was violated).
    *   **Fix**: Inspect the generated `TFREPORT.json` file. The detailed report will pinpoint the exact failure under `effects`, `policy`, `capabilities`, or `laws`.

*   **Error**: `unsupported node kind: <KIND>`
    *   **Cause**: The L0 file contains a node kind that the runtime executor in `run.mjs` does not recognize.
    *   **Fix**: Add the necessary logic to the `executeL0` function to handle the new node kind.

## Gaps

1.  **Code Duplication (Runtime)**: The L0 runtime (`packages/runtime/run.mjs`) re-implements the entire `Transform` logic, creating a near-exact copy of the `runTransform` function in `packages/transform/index.mjs`. This is a critical maintenance and correctness hazard.
2.  **Discoverability (Runtime)**: There is no CLI command to execute an L0 file directly. This makes it difficult for developers to test or debug the runtime behavior of a compiled pipeline without writing a custom script.
3.  **DX (Checker)**: The checker's output is a monolithic `TFREPORT.json` file. While comprehensive, it can be hard to quickly parse for the specific cause of a failure. A human-readable summary output to the console would improve the user experience.
4.  **Documentation (Z3 Harness)**: The Z3 integration is a powerful feature, but its mechanism, prerequisites (is Z3 bundled or a system dependency?), and how to write new Z3-backed laws are entirely undocumented.

## Next 3 improvements

1.  **Refactor the Runtime to eliminate duplicated Transform logic.**
    *   **Action**: Remove the `evaluateTransform` function from `packages/runtime/run.mjs` and have it import and use `runTransform` from `packages/transform/index.mjs` instead.
    *   **Impact**: Critical. Eliminates a major source of code duplication, reducing bugs and maintenance overhead.
    *   **Effort**: Small.

2.  **Create a `tf run` command to execute L0 files.**
    *   **Action**: Add a `run` command to the main CLI (`tools/tf-lang-cli/index.mjs`) that wraps the `executeL0` function, allowing a user to run an L0 file and see the resulting trace output.
    *   **Impact**: High. Makes the runtime discoverable and provides a direct way to test and observe pipeline execution.
    *   **Effort**: Medium.

3.  **Add a human-readable summary to the Checker's output.**
    *   **Action**: When not in a `--json` mode, the checker should print a concise summary of the results to `stdout`, highlighting which sections failed (e.g., "Effects: FAILED", "Laws (idempotency): PASSED").
    *   **Impact**: High. Improves the developer feedback loop by making it much faster to diagnose failures.
    *   **Effort**: Medium.