# Track D: Examples & Monitors

## What exists now

*   **Example Pipelines (L2)**: Two main L2 pipelines are provided under `examples/v0.6/pipelines/`:
    *   `auto.fnol.fasttrack.v1.l2.yaml`: An insurance claims fast-tracking process.
    *   `auto.quote.bind.issue.v2.l2.yaml`: An insurance quote-to-issue process.
*   **Example Monitor (L2)**: One monitor is provided: `examples/v0.6/monitors/fasttrack-24h.l2.yaml`.
*   **Build Artifacts (L0)**: Corresponding L0 JSON builds for the pipelines and monitor are present in `examples/v0.6/build/`.
*   **Tests**: Each example has a corresponding test spec under `examples/v0.6/tests/` (e.g., `fnol-fasttrack.spec.mjs`).
*   **Automation Script**: A shell script, `tasks/run-examples.sh`, exists to orchestrate the expansion, testing, and diagram generation for all examples.
*   **Diagrams**: The script generates `.dot` files in the `diagrams/` directory. It also attempts to create `.svg` files if the `dot` command-line tool is installed.

## How to run

The canonical way to run the examples is via the provided shell script:

```bash
bash tasks/run-examples.sh
```

This script is intended to:
1.  Expand L2 YAML pipelines/monitors into L0 JSON artifacts.
2.  Run checks to assert they are valid kernel-only L0 files.
3.  Execute the associated test specifications against the L0 files.
4.  Generate DOT and SVG diagrams from the L0 files.

**However, this script currently fails.**

## Common errors + fixes

*   **Error**: `invalid call syntax: transform.validate(schema: "FnolV1", input: "@receive.body") # types: in.input={schemaRef:"FnolV1",format:"json"}; out={schemaRef:"FnolV1",format:"json"}`
    *   **Cause**: The `run-examples.sh` script fails during the expansion of the first pipeline (`auto.fnol.fasttrack.v1.l2.yaml`). The YAML pre-processor in the expander (`packages/expander/expand.mjs`) incorrectly includes the comment (`# types: ...`) as part of the macro string, causing a parsing failure.
    *   **Fix**: Remove the inline comment from the `validate_fnol` step in the L2 YAML file. This allows the script to proceed, but reveals the underlying fragility of the parser.

## Gaps

1.  **Release Blocker (Broken Examples)**: The primary example workflow is broken out of the box. A new contributor running `tasks/run-examples.sh` will immediately hit a fatal error, creating a major onboarding hazard and blocking release.
2.  **DX (Fragile Parser)**: The root cause of the broken example is the fragile YAML pre-processor that cannot handle inline comments. This was also identified in Track B, but its impact is most visible here.
3.  **Documentation (Missing Guidance)**: There is no `README.md` in `examples/v0.6/` to explain what the examples are, what they demonstrate, or how to run them. A user has to discover the `run-examples.sh` script in a different directory (`tasks/`).
4.  **Diagrams (Tool Dependency)**: The script's ability to generate user-friendly SVG diagrams depends on the `dot` utility being installed on the system, but this dependency is not documented. If `dot` is missing, only the less accessible `.dot` files are created.

## Next 3 improvements

1.  **Fix the broken example pipeline.**
    *   **Action**: Remove the inline comment in `auto.fnol.fasttrack.v1.l2.yaml`. As a follow-up to the Track B recommendation, replace the fragile parser with a robust solution that ignores comments correctly.
    *   **Impact**: Critical. Unblocks the entire example workflow and allows for successful execution of `run-examples.sh`.
    *   **Effort**: Small (for the immediate fix), Medium (for the parser refactor).

2.  **Add a `README.md` to the `examples/v0.6/` directory.**
    *   **Action**: Create a `README.md` file that explains the purpose of each example, lists the per-example commands, and points to `tasks/run-examples.sh` as the main E2E script.
    *   **Impact**: High. Provides clear, contextual guidance for new developers wanting to understand the system through its examples.
    *   **Effort**: Small.

3.  **Document and handle the `dot` dependency gracefully.**
    *   **Action**: Add a note to the new `README.md` about the `dot` dependency for SVG generation and include installation instructions (e.g., `sudo apt-get install graphviz`). Modify the `run-examples.sh` script to print a clear warning if `dot` is not found, rather than failing silently.
    *   **Impact**: Medium. Improves the user experience by making diagram generation more reliable and transparent.
    *   **Effort**: Small.