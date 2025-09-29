# Review: D-Optimizer (v0.5)

This document reviews the developer experience and documentation for the Track D (Optimizer) toolchain.

## 1. What Exists Now

The optimizer is implemented in the `packages/tf-opt` package and provides a CLI tool, `tf-opt`. Its purpose is to read a low-level Intermediate Representation (IR) of a program, apply a series of rule-based rewrites (passes), and emit an optimized version of the IR.

The tool is designed to operate in two modes:
1.  **`--plan-only` (default):** Analyzes the IR and outputs a "rewrite plan," which is a JSON object listing the optimization opportunities ("laws") it found.
2.  **`--apply`:** Reads the IR, applies the rewrites, and outputs the new, optimized IR.

**CRITICAL ISSUE:** The tool is currently broken. Running `tf-opt --help` fails with a `SyntaxError` due to a missing module export. This makes it impossible to run any optimization passes. The following review is based on a source code analysis of its intended behavior.

## 2. Optimizer Passes & User Benefits

The optimizer's logic is located in `lib/rewrite-detect.mjs`. It inspects a sequence of operations ("primitives") and identifies patterns based on "laws." Each law corresponds to an optimization pass:

1.  **Idempotent Pass (`idempotent:*`)**
    -   **What it does:** Detects when the same operation is performed twice in a row (e.g., `set_user_name(...) |> set_user_name(...)`).
    -   **Benefit:** Reduces program size and eliminates redundant work, leading to faster execution and lower resource consumption.

2.  **Inverse Pass (`inverse:serialize-deserialize`)**
    -   **What it does:** Detects when a `serialize` operation is immediately followed by a `deserialize` operation. These two operations cancel each other out.
    -   **Benefit:** Improves speed by removing a computationally expensive and useless pair of operations.

3.  **Commutative Pass (`commute:emit-metric-with-pure`)**
    -   **What it does:** Detects when a metric emission (`emit-metric`) occurs next to a purely computational function. Since the order doesn't matter, it can reorder them.
    -   **Benefit:** Improves clarity and can enable further optimizations by grouping related operations together. This pass doesn't typically reduce size or speed on its own but is a key enabler for other passes.

## 3. How to Run (Hypothetical)

If the tool were working, a micro-benchmark recipe would look like this:

```bash
# Prerequisite: A sample program IR file (e.g., my_program.ir.json)
# This file does not exist in the repository, which is another gap.

# 1. Generate a rewrite plan to see what can be optimized
node packages/tf-opt/bin/opt.mjs --ir my_program.ir.json --plan-only

# 2. Apply the optimizations and generate the new IR
node packages/tf-opt/bin/opt.mjs --ir my_program.ir.json --apply --out my_program.opt.json

# 3. Compare the original and optimized files
# A user would typically use a diff tool to see the changes.
diff my_program.ir.json my_program.opt.json
```

## 4. Expensive Passes & Configuration

-   **Expensive Passes:** Based on the source code, none of the current passes appear computationally expensive. They involve a single linear scan over the primitive sequence. This is a positive design feature.
-   **Configuration:** There is no mechanism to enable or disable specific passes. The tool runs all implemented checks every time.

## 5. Gaps & DX Friction

1.  **The Tool is Broken:** The most severe issue. The `tf-opt` CLI fails on launch due to an internal `SyntaxError`. It is completely unusable.
2.  **No README:** The `packages/tf-opt` directory lacks a `README.md`, leaving a developer with no documentation on its purpose, how to run it, or the meaning of its output.
3.  **No Sample IR:** There are no example IR files in the repository. A new contributor has nothing to run the optimizer on, preventing them from testing or extending it.
4.  **No Pass Configuration:** A user cannot disable a specific pass. While the current passes are cheap, future, more expensive passes would require a way to be selectively disabled for faster development builds.

## 6. Next 3 Improvements

1.  **(S) Fix the `SyntaxError`:** The import error in `lib/plan-apply.mjs` must be fixed to make the tool runnable. This is a blocking issue.
2.  **(M) Create a Quickstart Guide:** Add a `README.md` to `packages/tf-opt` that includes:
    -   A one-sentence description of each optimization pass.
    -   A complete, working "How to Run" example, including a sample `my_program.ir.json` file that can be committed to the repository.
3.  **(L) Implement Pass Configuration:** Add a command-line flag (e.g., `--disable-pass <pass_name>`) to allow users to selectively disable optimization passes. This would improve the tool's flexibility for future development.