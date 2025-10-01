# Track B: Engine Core

## What exists now

*   **Expander**: The macro expander (`packages/expander/expand.mjs`) is responsible for converting L2 pipeline YAML files into L0 JSON DAGs. It recognizes a fixed set of macros (e.g., `interaction.request`, `state.merge`) and expands them into sequences of the four kernel primitives (`Transform`, `Publish`, `Subscribe`, `Keypair`). It also includes a pre-processor to handle multi-line macro invocations in YAML.
*   **Transform Runner**: The `Transform` primitive is executed by `packages/transform/index.mjs`. It's a pure function that dispatches on `spec.op` and handles operations like hashing (`blake3`), data manipulation (`concat`, `get`), schema validation (`jsonschema.validate`), and CRDT merges (`crdt.gcounter.merge`). It contains deterministic stubs for non-pure operations like model inference and policy evaluation.
*   **Keypair Generator**: Key generation is handled in `packages/entropy/keypair.mjs`. It currently supports `Ed25519` and deterministically generates a public key PEM and a stable `key_id` derived from a Blake3 digest. For test stability, it only returns public material.
*   **Instance Registry**: The v2 instance registry (`instances/registry.v2.json`) uses a rule-based system to map nodes to concrete backend implementations (e.g., `@HTTP`, `@Memory`). Rules are matched based on a node's `domain` and `channel`.

## How to run

The engine core components are not typically run directly but are invoked by higher-level CLI commands.

*   **Expand an L2 pipeline to L0 (implicitly invokes the expander)**:
    ```bash
    # This command is not yet aliased, showing an example of what it would do.
    # A script like `pipeline-expand.mjs` likely wraps this logic.
    node tools/tf-lang-cli/index.mjs <some_command_that_expands> examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
    ```
    *Note: A direct CLI for expansion is not obvious, it's a library function.*

*   **The Transform runner and Keypair generator are internal library functions** used by other parts of the system (like the runtime) and are not exposed via the CLI.

## Common errors + fixes

*   **Error**: `Unsupported macro: <macro_name>`
    *   **Cause**: The L2 pipeline YAML uses a macro that is not defined in the `MACROS` constant in `packages/expander/expand.mjs`.
    *   **Fix**: Implement the missing macro handler in the expander or correct the typo in the L2 YAML.

*   **Error**: `Unsupported transform op: <op_name>`
    *   **Cause**: An L0 file contains a `Transform` node with a `spec.op` that is not handled by the `runTransform` function in `packages/transform/index.mjs`.
    *   **Fix**: Add a case for the new operation in the `runTransform` switch statement.

## Gaps

1.  **Discoverability (Expander)**: The macro expansion logic is a core part of the engine, but there is no direct, documented CLI command to perform L2 to L0 expansion. Developers must find wrapper scripts (`pipeline-expand.mjs`) or infer its usage from tests.
2.  **Code Clarity (Expander)**: The `preprocessL2Yaml` function in `expand.mjs` uses a fragile, stateful loop with regex to wrap multi-line macros in quotes. This is a common source of parsing errors and is hard to debug. A more robust YAML parsing strategy is needed.
3.  **Extensibility (Transform Runner)**: The `runTransform` function is a single, large `switch` statement. Adding new operations requires modifying this central file, which can lead to merge conflicts and makes the code harder to maintain. A more modular, pluggable architecture would be better.
4.  **Documentation (Instance Registry)**: The structure and matching logic of the v2 instance registry are not documented. A contributor would need to read the `resolve.mjs` source to understand how to write rules or what the `default` key means.

## Next 3 improvements

1.  **Expose a dedicated `tf expand` CLI command.**
    *   **Action**: Add an `expand` command to `tools/tf-lang-cli/index.mjs` that takes an L2 YAML file and outputs the corresponding L0 JSON.
    *   **Impact**: High. Makes a core engine function discoverable and easy to use for local debugging and development.
    *   **Effort**: Small.

2.  **Refactor YAML macro parsing to use standard features.**
    *   **Action**: Remove the `preprocessL2Yaml` string manipulation hack. Instead, document and enforce the use of standard YAML block scalars (`|` or `>`) for multi-line macro invocations.
    *   **Impact**: High. Eliminates a fragile and error-prone part of the system, improving reliability.
    *   **Effort**: Medium.

3.  **Refactor the Transform Runner to be modular.**
    *   **Action**: Change `runTransform` from a large switch statement to a dispatch mechanism that uses a map of registered transform operations. Each op would be its own small function.
    *   **Impact**: Medium. Improves maintainability and makes it easier and safer to add new transform operations.
    *   **Effort**: Medium.