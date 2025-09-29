# Review: E-Proofs (v0.5)

This document reviews the developer experience and documentation for the Track E (Proofs) components, which use an SMT solver for formal verification.

## 1. What Exists Now

The proof system is implemented in `packages/tf-l0-proofs/src/`. It is not a runnable tool but a collection of JavaScript modules that generate SMT-LIB2 scripts. These scripts can then be checked by an external SMT solver (like Z3) to formally prove properties of the system.

-   **SMT Laws (`smt-laws.mjs`):** This file defines the core "laws" of the system as a set of axioms. These laws represent the formal guarantees that the system aims to provide.
-   **SMT Script Generation:** The `emitLaw` function in `smt-laws.mjs` can take the name of a law and generate a self-contained SMT script to check its validity.

## 2. The Proof Boundary: Guarantees & Assumptions

The "proof boundary" defines what is guaranteed by the system. These guarantees are encoded as formal laws.

**What's Guaranteed (The Laws):**

1.  **`idempotent:hash`:** Hashing the same value twice is the same as hashing it once. `H(H(x)) = H(x)`.
2.  **`inverse:serialize-deserialize`:** Serializing a value and then deserializing it returns the original value. `D(S(v)) = v`.
3.  **`commute:emit-metric-with-pure`:** Emitting a metric and performing a pure computation can be done in either order without changing the result. `E(H(x)) = H(E(x))`.

**What's Assumed:**

-   **An SMT Solver Exists:** The system assumes the developer has an SMT solver (like Z3) installed and available in their `PATH`. The tooling does not provide or bundle a solver.
-   **The SMT Model is Correct:** The proofs are only as good as the model defined in `smt-laws.mjs`. It assumes the functions (`H`, `S`, `D`, etc.) accurately represent the behavior of their real-world counterparts.
-   **`idempotent:write-by-key` is a Negative Test:** This law is confusingly named. Its axiom `(assert (not (= twice once)))` actually proves that writing the same key twice with a new value is *not* the same as writing it once. It's a check for non-idempotence, not idempotence. This is a significant documentation hazard.

## 3. How to Run Checks Locally

There is no single command to run the proofs. A developer must manually generate an SMT script and pipe it to an SMT solver.

**Hypothetical Quickstart (using Node.js and Z3):**

```bash
# Prerequisite: Install Z3 (e.g., `brew install z3`)

# 1. Create a script to generate the proof for a law.
#    Save this as `run-proof.mjs`:
#    -------------------------------------------------
import { emitLaw } from './packages/tf-l0-proofs/src/smt-laws.mjs';
const lawName = process.argv[2];
if (!lawName) {
  console.error('Usage: node run-proof.mjs <law-name>');
  process.exit(1);
}
console.log(emitLaw(lawName));
#    -------------------------------------------------

# 2. Run the script and pipe the output to Z3.
#    This example checks the 'inverse:serialize-deserialize' law.
node run-proof.mjs inverse:serialize-deserialize | z3 -in

# Expected Output for a valid proof:
# sat

# Expected Output for a failed proof (or an invalid law):
# unsat
```

## 4. Troubleshooting Proofs

-   **Failure Pattern: `unsat`**
    -   **Meaning:** The solver proved that the axioms in the law are contradictory. For the `(assert (not ...))` style of check, `unsat` means the property holds (the negation is unsatisfiable). For a positive assertion, `unsat` means the law is broken. This is deeply confusing for newcomers.
    -   **Likely Fix:** This indicates a fundamental problem in the law's definition or the underlying axioms. The developer must analyze the logic of the SMT script to understand the contradiction.

-   **Failure Pattern: `(error "...")` from Z3**
    -   **Meaning:** The generated SMT script is syntactically incorrect.
    -   **Likely Fix:** This points to a bug in the `emitLaw` function or the data structures in `smt-laws.mjs`.

-   **Failure Pattern: `Unknown law: ...`**
    -   **Meaning:** The law name passed to the script is not defined in `LAWS`.
    -   **Likely Fix:** Check for typos or consult `smt-laws.mjs` for the list of available laws.

## 5. Gaps & DX Friction

1.  **No Proof Runner:** The biggest gap is the lack of an integrated tool to run the proofs. A developer must manually wire up Node.js and an SMT solver, which is a significant barrier to entry.
2.  **No Documentation:** The `packages/tf-l0-proofs` directory has no `README.md`. A developer has no guidance on the purpose of the proofs, how to run them, or how to interpret the results.
3.  **SMT Solver is an Unstated Dependency:** The need for an external tool like Z3 is not documented anywhere.
4.  **Confusing Law Naming:** The `idempotent:write-by-key` law does the opposite of what its name implies, creating a major potential for misunderstanding.
5.  **`sat` vs. `unsat` Interpretation:** The meaning of `sat` and `unsat` depends on the structure of the assertion (`(assert (not ...))` vs. `(assert ...)`). This is a classic SMT pitfall that is not explained for a new user.

## 6. Next 3 Improvements

1.  **(M) Create a Proof Runner Script:** Add a script to the root `package.json` (e.g., `pnpm test:proofs`) that automatically runs all defined laws through Z3 (if available) and reports a clear "pass" or "fail" for each. The script should detect if Z3 is not installed and provide a helpful error message.
2.  **(M) Write a "Proofs 101" Guide:** Create a `README.md` in `packages/tf-l0-proofs` that explains:
    -   What SMT is and why it's being used.
    -   How to install Z3.
    -   How to run the new `test:proofs` script.
    -   A clear explanation of each law, correcting the confusing name of `idempotent:write-by-key`.
    -   How to interpret `sat` and `unsat` in the context of the project's assertions.
3.  **(S) Rename the Confusing Law:** Rename `idempotent:write-by-key` to something more accurate, like `write_is_not_idempotent_on_value_change`, to prevent confusion.