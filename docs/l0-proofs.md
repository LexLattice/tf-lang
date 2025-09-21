# L0 Proof Artifacts

The proof emission workflow produces deterministic artifacts for a small set of reference flows without invoking any solvers.

## Outputs

The emitter records the following files under `out/0.4/proofs/`:

- Alloy structural models for the storage conflict and storage ok flows.
- SMT encodings of the structural constraints for the same flows.
- SMT law encodings for the `idempotent:hash`, `inverse:serialize-deserialize`, and `commute:emit-metric-with-pure` laws.
- SMT property encodings for the parallel safety of `storage_conflict.tf` and the commute equivalence between `obs_pure_EP.tf` and `obs_pure_PE.tf`.

A deterministic `index.json` summarizes the generated files and uses a fixed timestamp to keep CI runs reproducible.

## CI Artifacts

Every pull request runs the **L0 Proof Artifacts** workflow. Its `l0-proofs` artifact contains the files listed above. To download it:

1. Open the PR in GitHub.
2. Navigate to **Actions → Artifacts**.
3. Download the `l0-proofs` bundle.

## Local Reproduction

To regenerate the artifacts locally:

```sh
pnpm -w -r build
node scripts/proofs-emit-all.mjs
```

The `scripts/proofs-emit-all.mjs` orchestrator ensures all proof files appear under `out/0.4/proofs/`.

> **Note:** CI only emits the artifacts. To run solvers manually, use `z3 -smt2 <file.smt2>` for SMT outputs or open Alloy files in the Alloy IDE.
