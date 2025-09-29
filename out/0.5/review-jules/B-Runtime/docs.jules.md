# Review: B-Runtime (v0.5)

This document reviews the developer experience and documentation for the Track B (Runtime) components.

## 1. What Exists Now

The core runtime is implemented in the `packages/tf-lang-l0-ts` package. It consists of:

-   **A Virtual Machine (VM):** The `src/vm/interpreter.js` file contains a VM capable of executing a JSON-based bytecode format (L0).
-   **A Host Interface:** The VM interacts with the external world through a `Host` interface (`src/vm/opcode.js`), which provides capabilities like state access (`lens_project`, `lens_merge`) and calling external trusted functions (`call_tf`). A `DummyHost` for in-memory execution is also provided.
-   **Test Vector Runner:** A script at `scripts/run-vectors.ts` serves as a test harness and the primary example of how to run the VM. It executes programs defined in JSON files located in `tests/vectors/`.

## 2. How to Run: Minimal Runtime Demo

The intended way to run a program is to use the test vector runner. This process loads a JSON file, executes its bytecode, and verifies the final state.

**Prerequisite:** The package must be built.

```bash
# 1. Compile the runtime code (one-time setup)
pnpm -C packages/tf-lang-l0-ts build

# 2. Run the test vector script
# This will execute all *.json files in the tests/vectors/ directory.
pnpm -C packages/tf-lang-l0-ts vectors

# Expected Output:
# ✓ lens mod canonicalizes negative numbers
# ✓ ... (more passing tests)
```

**Anatomy of a Runtime Demo (`tests/vectors/lens_mod.json`):**

-   **Input (Initial State):** The program starts with an initial state, defined by the first `CONST` instruction writing to register 0.
    ```json
    { "op": "CONST", "dst": 0, "value": { "n": -3 } }
    ```
-   **Program (Bytecode):** A series of instructions performs a calculation. This example calls an external function (`tf://lens/mod@0.1`) and merges the result back into the state.
    ```json
    { "op": "CALL", "dst": 3, "tf_id": "tf://lens/mod@0.1", "args": [1, 2] },
    { "op": "LENS_MERGE", "dst": 0, "state": 0, "region": "/n", "sub": 3 }
    ```
-   **Output (Expected Delta):** The `expected` block defines the expected change (`delta`) to the initial state. The runner verifies that the VM's output matches this delta.
    ```json
    "expected": {
      "delta": { "replace": { "n": 2 } }
    }
    ```

## 3. Error Modes, Timeouts, and Retries

-   **Error Modes:** Errors are handled via standard JavaScript exceptions. The test vector format has an `"expected": { "error": "..." }` field, which indicates that a specific error message is the correct outcome. Common errors include `VM_BAD_ACCESS` for out-of-bounds register access.
-   **Timeouts & Retries:** There are **no built-in mechanisms for timeouts or retries.** The VM will run until it halts or throws an unhandled exception. Any long-running operation or retry logic must be implemented by the *host* application that calls the VM, not within the VM itself. This is a critical design detail that needs to be documented.
-   **Resource Prerequisites:** The runtime itself is self-contained and has no external resource needs beyond Node.js. However, the `Host` implementation that is provided to the VM may have its own prerequisites (e.g., database connections, network access).

## 4. Gaps & DX Friction

1.  **No Standalone Runner:** There is no simple command-line tool to execute a single bytecode file. The only way to run a program is via the `vectors` script, which is designed as a test harness for the entire suite, not for single-file execution. This makes debugging a specific program difficult.
2.  **Implicit Timeout/Retry Policy:** The lack of built-in timeout and retry handling is a major architectural feature that is completely undocumented. A developer using the VM would have to discover this by reading the source code.
3.  **Host Implementation is Undocumented:** The `Host` interface is the primary way to integrate the VM into a larger application, but its responsibilities and contract are not formally documented. One must read the `run-vectors.ts` script to see how a `DummyHost` is implemented and used.

## 5. Next 3 Improvements

1.  **(M) Create a CLI Runner:** Build a simple CLI tool (e.g., `bin/run.mjs`) in the `tf-lang-l0-ts` package that takes a single vector JSON file as an argument and prints the resulting delta or error. This would vastly improve the debugging loop.
2.  **(S) Document the Runtime Philosophy:** Add a section to the `README.md` titled "Execution Model" that explicitly states:
    -   The VM is single-threaded and synchronous.
    -   Timeouts and retries are the responsibility of the host environment.
    -   Resource management is delegated to the host.
3.  **(M) Document the Host Interface:** Add a `docs/host-interface.md` file that formally describes the purpose and expected behavior of each method in the `Host` interface. Provide a minimal example of a custom host implementation.