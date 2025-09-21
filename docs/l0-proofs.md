# L0 Proofs

## Law obligations

We encode algebraic laws for core primitives as small SMT-LIB v2 obligations. Use the CLI to emit either standalone axioms or flow equivalence checks:

```bash
node scripts/emit-smt-laws.mjs --law idempotent:hash -o out/0.4/proofs/laws/idempotent_hash.smt2
node scripts/emit-smt-laws.mjs --equiv examples/flows/info_roundtrip.tf examples/flows/info_roundtrip.tf \
  --laws idempotent:hash,inverse:serialize-deserialize \
  -o out/0.4/proofs/laws/roundtrip_equiv.smt2
```

The generated files assert the relevant axioms, compare symbolic outputs, and end with `(check-sat)`. CI does not invoke an SMT solver—these files are produced for human review and audit trails alongside our Alloy exports.

Current obligations are structural over uninterpreted functions and deliberately ignore primitive arguments. They justify algebraic rewrites (idempotency, inverse, commutation) rather than semantic equality of parameterized calls. We plan to model arguments later—likely by indexing symbols—but that work is outside D2’s scope.

See also the [SMT emitter](../scripts/emit-smt.mjs) and [Alloy exporter](../scripts/emit-alloy.mjs) for the broader proof pipeline.
[`scripts/proofs-emit-all.mjs`](../scripts/proofs-emit-all.mjs) orchestrates the
full bundle we publish in CI.

# L0 Proof Artifacts

The L0 proofs focus on deterministic encodings for a representative set of
flows and algebraic laws. We currently emit four categories:

- **Alloy structural models** – `.als` modules for the storage conflict flows.
- **SMT structural constraints** – `.smt2` encodings of the same flows.
- **SMT laws** – idempotent hash, serialize/deserialize inverse, and
  `emit-metric-with-pure` commutation axioms.
- **SMT properties** – a parallel safety obligation plus an observational
  equivalence check for pure observer flows.

All emitters annotate IR nodes with catalog-derived write URIs before
generating encodings, so runs require the A0/A1 catalog steps.

## Generate proofs locally

1. Install Node 20 and pnpm (see [`toolchain/.node-version`](../toolchain/.node-version)) and install dependencies:
   ```bash
   pnpm install
   pnpm run a0 && pnpm run a1
   pnpm -w -r build
   ```
2. Emit the full artifact set with the convenience script:
   ```bash
   node scripts/proofs-emit-all.mjs
   ```
   The command mirrors the CI bundle and writes `out/0.4/proofs/index.json` for
   easy inspection. You can also run `pnpm run proofs:emit`.
3. (Optional) Emit individual files directly using the commands in the section
   above if you only need a specific encoding.

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

The **L0 Proof Artifacts** workflow runs on every pull request (and via manual
dispatch). It installs the workspace, executes `pnpm run a0`/`pnpm run a1`,
builds the packages, and invokes the bundle script to upload an artifact named
`l0-proofs`.

To download the proofs:

1. Open the pull request and navigate to **Actions → L0 Proof Artifacts**.
2. Select the latest run for your branch and download the `l0-proofs` artifact.
3. Extract the archive to access the `.als`, `.smt2`, and `index.json` files
   under `out/0.4/proofs/`.

These artifacts provide a deterministic snapshot of the conflict analysis,
algebraic laws, and sample property checks without running solvers in CI.
