# L0 Proofs

## Artifact overview

We emit four proof families for representative flows and laws. Each artifact lives under `out/0.4/proofs/` and is listed in a de
terministic `index.json` with a fixed timestamp.

- **Alloy (structural)** – `storage_conflict.als`, `storage_ok.als`
- **SMT (structural constraints)** – `storage_conflict.smt2`, `storage_ok.smt2`
- **SMT laws (axioms + 1 equivalence)** – `laws/idempotent_hash.smt2`, `laws/inverse_roundtrip.smt2`, `laws/emit_commute.smt2`
- **SMT properties (flow obligations)** – `props/storage_conflict.smt2`, `props/obs_pure_equiv.smt2`

The Alloy files expand the IR into explicit `Prim`, `Par`, and `Seq` structures. The SMT encodings assert the absence of conflicti
ng writes, law axioms, and equivalence checks. CI only generates these inputs; solver runs remain manual.

## CI workflow

The **L0 Proof Artifacts** workflow runs on every pull request and via manual dispatch. It performs the following steps:

1. Check out the repository and install the workspace with Node 20 + pnpm via the shared composite action.
2. Execute `pnpm run a0`, `pnpm run a1`, and `pnpm -w -r build` to materialize catalogs and build the packages.
3. Invoke `node scripts/proofs-emit-all.mjs` to emit the artifacts listed above.
4. Upload the resulting `out/0.4/proofs/**` directory as an artifact named `l0-proofs`.

### Downloading artifacts

1. Open the pull request and expand the **L0 Proof Artifacts** check.
2. Locate the **Artifacts** panel and download `l0-proofs`.
3. Extract the archive to inspect the `.als` and `.smt2` files under `out/0.4/proofs/`.

## Local generation

Install Node 20 + pnpm (see [`toolchain/.node-version`](../toolchain/.node-version)) and install dependencies:

```bash
pnpm -w -r install --frozen-lockfile
pnpm run a0
pnpm run a1
```

Emit all proof artifacts with the convenience script:

```bash
pnpm -w -r build
node scripts/proofs-emit-all.mjs
```

The script creates the output directory, calls the individual Alloy/SMT emitters, and writes a deterministic `index.json`. You ca
n also access the underlying emitters directly—`scripts/emit-alloy.mjs`, `scripts/emit-smt.mjs`, `scripts/emit-smt-laws.mjs`, and 
`scripts/emit-smt-props.mjs`—for ad-hoc experiments.

## Optional solver checks

CI does not invoke solvers. To experiment locally:

- Run `z3 -smt2 <file>.smt2` against any SMT obligation.
- Open the `.als` files in [Alloy Analyzer](https://alloytools.org/) and explore the built-in `run` commands.

These checks remain advisory; `storage_conflict` is expected to produce a conflict witness, while `storage_ok` should validate.
