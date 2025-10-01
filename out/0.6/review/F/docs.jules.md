# Track F: Types & Capabilities

## What exists now

*   **Typecheck CLI**: A `typecheck` command is available via the main CLI (`tools/tf-lang-cli/index.mjs`). Its logic is implemented in `packages/typechecker/typecheck.mjs`. The tool inspects an L0 file and compares the types of variables flowing between nodes.
*   **Port Typing**: Type information is read from a `metadata.port_types` block inside an L0 node. The typechecker parses `in` and `out` sections, resolving expected types for each input port and recording the types for each output variable.
*   **Adapter Registry**: The typechecker can suggest adapters for type mismatches. It loads these from a JSON file, defaulting to `adapters/registry.json`. Adapters are defined by their `op`, a `from` type descriptor, and a `to` type descriptor.
*   **Capability Lattice**: A capability lattice, defined in `policy/capability.lattice.json`, maps channel patterns (`rpc:req:*`) and keypair algorithms (`Ed25519`) to specific capability strings (e.g., `cap:publish:rpc:req:*`). This is used by the main checker (`packages/checker/check.mjs`) to determine the set of capabilities an L0 pipeline requires.

## How to run

*   **Run the typechecker on an L0 file**:
    ```bash
    node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
    ```

*   **Run the typechecker with a custom adapter registry**:
    ```bash
    node tools/tf-lang-cli/index.mjs typecheck <L0_FILE> --adapters <PATH_TO_REGISTRY>.json
    ```

## Common errors + fixes

*   **Error**: Type mismatch reported by the checker.
    *   **Cause**: A variable produced by one node has a type descriptor that does not match the type expected by a consuming node's input port.
    *   **Fix**:
        1.  Correct the type definition in the `metadata.port_types` of one of the nodes.
        2.  If the mismatch is intentional, create and register an adapter in `adapters/registry.json` to bridge the two types. The typechecker will then suggest this adapter instead of reporting an error.

*   **Error**: `failed to load adapter registry at <PATH>`
    *   **Cause**: The `--adapters` flag points to a non-existent or malformed JSON file.
    *   **Fix**: Ensure the path is correct and the file is valid JSON with an `adapters` array.

## Gaps

1.  **DX (No Autofix/Codegen for Adapters)**: The typechecker can *suggest* an adapter is needed but provides no way to automatically apply it. A developer must manually insert a new `Transform` node into the L0 file with the correct `spec.op`. This is tedious, error-prone, and requires manual editing of a generated file, which `AGENTS.md` discourages.
2.  **Documentation (Port Typing Syntax)**: The syntax for defining port types in the `metadata.port_types` block is complex and undocumented. Features like wildcard (`*`) and default ports are used in the typechecker logic but are not explained anywhere.
3.  **Incompleteness (Capability Lattice)**: The capability lattice in `policy/capability.lattice.json` only covers `rpc:*` channels. Other channels used in the examples (e.g., `metric:*`, `policy:enforce`) are not defined, meaning the checker will not derive any required capabilities for them. This creates a security and policy blind spot.
4.  **Code Clarity (Type Descriptor Logic)**: The typechecker contains multiple functions (`normalizeDescriptor`, `extractDescriptor`, `selectNext`) with complex, overlapping logic for parsing and resolving type descriptors. This code is hard to follow and maintain.

## Next 3 improvements

1.  **Add an `--autofix` or `--apply-adapters` mode to the typechecker.**
    *   **Action**: When a mismatch is found and a unique adapter exists, allow the typechecker to automatically insert the required `Transform` node into the L0 DAG, rewriting variable references accordingly. This should happen at the L0 level, not by modifying L2 source.
    *   **Impact**: High. Drastically improves the developer experience by automating the tedious and error-prone task of applying adapters.
    *   **Effort**: Large.

2.  **Document the port typing and capability lattice schemas.**
    *   **Action**: Create a `docs/0.6/port-typing.md` guide that explains the full syntax for `metadata.port_types`, including wildcards and default fallbacks. Similarly, document the structure of the capability lattice file.
    *   **Impact**: High. Makes core features usable and extensible for contributors.
    *   **Effort**: Medium.

3.  **Complete the capability lattice definitions.**
    *   **Action**: Add entries to `policy/capability.lattice.json` for all channel types used in the v0.6 examples, including `metric:*`, `policy:enforce`, and `policy:record`.
    *   **Impact**: High. Closes a significant gap in the security and policy enforcement mechanism.
    *   **Effort**: Small.