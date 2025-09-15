# Acceptance — T1_2

## Evidence
- `oracles/core/` package directory.
- Oracle interfaces and result type definitions.
- Oracle stubs with unit tests.
- JSON and Markdown output for explainable failures.

## CI
- Job **`oracle-core`**:
  - Builds the `oracles/core` package.
  - Runs unit tests for the oracle stubs.
  - Verifies that oracles are pure, deterministic, and side-effect free.

## Determinism
- Oracles must be deterministic, always producing the same result for the same input.

## Docs
- README file in `oracles/core/` explaining the purpose and usage of the oracle library.
