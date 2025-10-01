# Track E: L1 Macro Growth & Laws

## What exists now

*   **Macro Definitions**: A suite of L1 macros for state, process, and policy are defined in `packages/expander/expand.mjs`. These include:
    *   `state.snapshot`, `state.version`, `state.diff`, `state.merge`
    *   `process.retry`, `process.await.any`, `process.await.all`, `process.timeout`, `process.saga`
    *   `policy.evaluate`, `policy.enforce`
*   **Law Attachment**: The `state.merge` macro demonstrates how algebraic laws are attached to L0 nodes. When the `strategy` is `crdt.gcounter`, it explicitly adds `associative`, `commutative`, and `idempotent` law IDs to the `Transform` node's metadata. For `jsonpatch`, it correctly notes the absence of such laws.
*   **Law Modules**: The `laws/` directory contains modules for checking specific properties, such as `crdt-merge.mjs` and `idempotency.mjs`.
*   **Authentication Ops**: Low-level authentication operations (`auth.mint_token`, `auth.check_token`) are implemented as pure functions in `packages/ops/auth.mjs` and exposed as `Transform` ops in `packages/transform/index.mjs`.

## How to run

The macros and laws are exercised via higher-level tools, not run directly.

*   **Using a macro**: Define it in an L2 pipeline YAML file. The expander processes it automatically.
    ```yaml
    # examples/v0.6/pipelines/some_pipeline.l2.yaml
    steps:
      - merge_state: state.merge(strategy: "crdt.gcounter", base: "@...", patch: "@...")
    ```
*   **Checking laws**: The `tf-checker` (`packages/checker/check.mjs`) orchestrates law verification, but the implementation is incomplete. The `crdt-merge.mjs` law, for instance, runs a static set of hardcoded samples and does not dynamically check the L0 file.

## Common errors + fixes

*   **Error**: `state.merge: unsupported strategy <STRATEGY>`
    *   **Cause**: Using an unknown strategy (e.g., `lww`) in the `state.merge` macro.
    *   **Fix**: Implement the new strategy in the `expandStateMerge` function in `packages/expander/expand.mjs` and add a corresponding transform op.

*   **Logical Error (Not a Crash)**: A `state.merge` operation with `jsonpatch` might be used in a context where commutativity is expected, leading to race conditions.
    *   **Cause**: The system correctly identifies that `jsonpatch` has no algebraic laws, but there is no gate to prevent its misuse in parallel execution paths.
    *   **Fix**: This is a design-time issue. The developer must ensure that order-sensitive operations are correctly sequenced in the L2 pipeline. The tool does not automatically prevent this class of error.

## Gaps

1.  **Release Blocker (Disconnected Law Checking)**: The law verification system is fundamentally flawed. The `state.merge` macro attaches law IDs to L0 nodes, but the corresponding law checker (`laws/crdt-merge.mjs`) **does not read or use them**. Instead, it runs a few hardcoded, static examples. This creates a dangerous illusion of verification; the system is not actually checking the algebraic properties of the code being submitted.
2.  **Missing Macros (Auth)**: The track scope includes `auth` macros, but they are not implemented in the expander. While `auth.*` *operations* exist in the transform layer, they are not exposed as first-class L1 macros, making them inaccessible from L2 pipelines.
3.  **Documentation (Law System)**: The mechanism for attaching laws and the process for creating a new law checker are completely undocumented. It's unclear how a contributor would add verification for a new algebraic property.
4.  **Inconsistent Naming (await)**: The `process.await.any` and `process.await.all` macros accept `sources`, `targets`, or `inputs` as the key for the array of events to wait for. This inconsistency is confusing and should be standardized to a single key (e.g., `sources`).

## Next 3 improvements

1.  **Fix the law checking system to be dynamic.**
    *   **Action**: Modify the `tf-checker` to iterate through the nodes of the input L0 file. When it finds a node with attached `laws`, it must dynamically load and execute the corresponding law checker against that specific node's properties. The static sample check in `crdt-merge.mjs` should be replaced with this dynamic logic.
    *   **Impact**: Critical. Fixes a major correctness and security gap, ensuring that declared algebraic properties are actually verified.
    *   **Effort**: Large.

2.  **Implement the missing `auth.*` L1 macros.**
    *   **Action**: Create `auth.mint_token` and `auth.check_token` macros in `packages/expander/expand.mjs` that wrap the existing `Transform` operations.
    *   **Impact**: High. Fulfills a key requirement of the v0.6 feature set and makes authentication capabilities available to L2 pipeline authors.
    *   **Effort**: Medium.

3.  **Document the macro and law extension process.**
    *   **Action**: Create a `docs/0.6/extending-macros.md` guide that explains how to add a new macro to the expander, how to attach laws, and how to create a corresponding law checker module.
    *   **Impact**: High. Empowers contributors to extend the language with new, verified abstractions.
    *   **Effort**: Medium.