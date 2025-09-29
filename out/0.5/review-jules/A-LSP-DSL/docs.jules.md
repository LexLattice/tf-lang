# Review: A-LSP-DSL (v0.5)

This document reviews the developer experience and documentation for Track A, covering the A1 (LSP Proto) and A4 (DSL Ergonomics) components.

## 1. What Exists Now

-   **A1 LSP Proto:** A basic Language Server Protocol (LSP) server is implemented in the `packages/tf-lsp-server` package. A corresponding VS Code client extension exists in `clients/vscode-tf`, which provides syntax highlighting for `.tf` files.
-   **A4 DSL Ergonomics:** The core language is defined in `packages/tf-lang-l0-ts`. However, it is not a human-writable DSL with a parser. Instead, it's a low-level, JSON-based bytecode format. The `examples/min.json` file shows a program defined by a list of instructions like `{"op": "CONST", "dst": 0, "value": null}`.

## 2. How to Run: The "First Result" Challenge

A "first result" for the LSP would be opening a `.tf` file in a development instance of VS Code and seeing diagnostics or getting code completions. Currently, this is extremely difficult for a new contributor.

**The Missing Quickstart:**

1.  **Build the Server:** The LSP server must be compiled:
    ```bash
    pnpm -C packages/tf-lsp-server build
    ```
2.  **Build the Client:** The VS Code extension must also be compiled:
    ```bash
    pnpm -C clients/vscode-tf build
    ```
3.  **Launch the Extension:** This is the critical gap. There is **no launch configuration (`.vscode/launch.json`)** provided in the repository. A developer must manually create one to run the extension in a new VS Code window [Extension Host]. Without this, there is no "press F5" to debug and see the LSP in action.

## 3. DSL Ergonomics & Glossary

-   **Parser Ergonomics:** There are none. Since the "language" is a JSON instruction set, there is no parser to speak of. Error surfaces would relate to malformed JSON or invalid instruction schemas, not syntax errors. This is a major ergonomic issue, as writing logic directly in this format is not feasible.
-   **Glossary of Terms:**
    -   **L0:** The foundational "Level 0" language, which is a low-level, bytecode-like Intermediate Representation (IR).
    -   **Instruction (`instr`):** A single operation in the L0 bytecode (e.g., `CONST`, `HALT`).
    -   **Register (`reg`):** A temporary storage location within the L0 VM.
    -   **Host:** The environment in which the L0 VM runs, providing capabilities like I/O.
    -   **LSP:** Language Server Protocol, a standard for providing language features like autocomplete and diagnostics to code editors.

## 4. Common Errors + Fixes

-   **ERROR:** Running the VS Code extension fails or the LSP doesn't start.
    -   **Reason:** The server or client packages have not been compiled from TypeScript. The `dist/` directories are missing.
    -   **Fix:** Run `pnpm build` within both `packages/tf-lsp-server` and `clients/vscode-tf`.
-   **CONFUSION:** "How do I write a simple program?"
    -   **Reason:** The lack of a high-level language and parser is undocumented. Developers will look for a syntax guide that doesn't exist.
    -   **Fix:** The documentation must clearly state that L0 is a compilation target (an IR) and not a language for direct authoring.

## 5. Gaps & DX Friction

1.  **No LSP Quickstart:** The single biggest gap is the missing `.vscode/launch.json` file. A new developer cannot easily run the LSP server and see it working. This makes the "10-minute quickstart" impossible.
2.  **Missing READMEs:** Key packages (`tf-lsp-server`) lack `README.md` files entirely. Existing READMEs (`clients/vscode-tf`) are stubs with no actionable instructions.
3.  **Misleading "DSL" Terminology:** The term "DSL" is a misnomer. The project currently defines a bytecode IR, not a Domain-Specific Language. This creates incorrect expectations for new contributors, who will search for a parser and syntax that do not exist.
4.  **No Sample Broken Inputs:** There are no examples of malformed L0 JSON files and what errors the LSP or a validator would produce.

## 6. Next 3 Improvements

1.  **(S) Add a VS Code Launch Configuration:** Add a working `.vscode/launch.json` to the repository root that allows a developer to compile the necessary packages and launch the VS Code extension with a single keystroke (F5).
2.  **(M) Create a "Hello World" LSP Tutorial:** Write a `README.md` for `clients/vscode-tf` that walks a developer through the entire process: building the code, launching the extension, creating a sample `.tf` file (even if it does nothing), and seeing a diagnostic message.
3.  **(M) Clarify the "Language" Strategy:** Add a top-level document (`docs/language.md`) that explains the current state. It should explicitly state that L0 is a JSON-based IR and that a higher-level, human-writable language is a future goal, not a current reality. This will correctly set expectations.