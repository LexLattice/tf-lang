# Lean 4 Prover Roadmap

The SMT shim uses Z3 today for lightweight implication checks. This folder will
hold a future Lean 4 setup once we move beyond the stub harness:

- `lakefile.toml` to pin Lean/Mathlib versions.
- `lake exe cache get` bootstrap scripts for CI.
- Skeleton proofs for the idempotency and CRDT merge laws, kept in sync with the
  Node harness.

Nothing is wired yet; the README simply stakes out the structure so we can land
Lean when the math library dependencies settle.
