# L0 Proof Artifacts

The L0 proofs focus on detecting storage write conflicts across parallel branches. Two emitters cover the default encodings:

- **D1 (SMT / Z3)** – generates `.smt2` programs that assert the absence of duplicate write URIs. We rely on [`scripts/emit-smt.mjs`](../scripts/emit-smt.mjs) to translate a flow into the solver input.
- **D3 (Alloy)** – produces `.als` models with explicit `Prim`, `Par`, and `Seq` structures plus predicates for write conflicts. [`scripts/emit-alloy.mjs`](../scripts/emit-alloy.mjs) handles the translation.

Both emitters annotate IR nodes with catalog-derived write URIs before generating encodings, so runs require the A0/A1 catalog steps.

## Generate proofs locally

1. Install Node 20 and pnpm (see [`toolchain/.node-version`](../toolchain/.node-version)) and install dependencies:
   ```bash
   pnpm -w -r install --frozen-lockfile
   pnpm run a0 && pnpm run a1
   ```
2. Emit SMT and Alloy artifacts for the storage flows:
   ```bash
   node scripts/emit-smt.mjs examples/flows/storage_conflict.tf -o out/0.4/proofs/storage_conflict.smt2
   node scripts/emit-smt.mjs examples/flows/storage_ok.tf -o out/0.4/proofs/storage_ok.smt2
   node scripts/emit-alloy.mjs examples/flows/storage_conflict.tf -o out/0.4/proofs/storage_conflict.als
   node scripts/emit-alloy.mjs examples/flows/storage_ok.tf -o out/0.4/proofs/storage_ok.als
   ```
   The scripts create `out/0.4/proofs/` if it does not already exist.

## Check SMT proofs with Z3 (optional)

Install a recent [Z3](https://github.com/Z3Prover/z3) build or use a container image. Run the solver against either SMT file:

```bash
z3 -smt2 out/0.4/proofs/storage_ok.smt2
z3 -smt2 out/0.4/proofs/storage_conflict.smt2
```

Interpretation in this encoding:

- `sat` ⇒ every checked parallel branch avoids conflicting writes.
- `unsat` ⇒ at least one branch pair writes to the same URI (a conflict witness exists).

`storage_ok` should report `sat`, while `storage_conflict` is expected to be `unsat` because two branches write the same resource.

## Explore Alloy models

Open the generated `.als` files in [Alloy Analyzer](https://alloytools.org/). The module defines two `run` commands:

- `run { some p: Par | Conflicting[p] }` searches for a counterexample demonstrating a conflict.
- `run { all p: Par | NoConflict[p] }` checks that no conflict occurs.

Use the default scope or supply one (for example, run the CLI with `--scope 6`) if you want Alloy to consider more nodes.

## CI artifacts

The **L0 proof artifacts** workflow runs on every pull request (and via manual dispatch). It installs the workspace, executes `pnpm run a0`/`pnpm run a1`, emits the four proof files listed above, and uploads them as an artifact bundle named `l0-proofs`.

To download the proofs:

1. Open the pull request and expand the **L0 proof artifacts** check.
2. Scroll to the **Artifacts** section and download `l0-proofs.zip`.
3. Extract the archive to access the `.smt2` and `.als` files under `out/0.4/proofs/`.

These artifacts provide a deterministic snapshot of the conflict analysis for the key storage flows without running solvers in CI.
