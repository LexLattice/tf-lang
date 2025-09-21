# L0 Proofs

## Artifact bundle overview

The automated proof bundle ships four deterministic emit categories:

- **Alloy structural** encodings for the storage conflict samples.
- **SMT structural** encodings for the same flows.
- **SMT laws** capturing algebraic axioms and a sample equivalence check.
- **SMT properties** covering a parallel safety proof and a commute equivalence pair.

Run `pnpm -w -r build` once after `pnpm run a0 && pnpm run a1`, then execute either command below to regenerate the full bundle locally:

```bash
node scripts/proofs-emit-all.mjs
# or
pnpm run proofs:emit
```

For a single-shot rebuild plus directory listing, run:

```bash
pnpm -w -r build && node scripts/proofs-emit-all.mjs && tree out/0.4/proofs
```

The outputs land under `out/0.4/proofs/` alongside a deterministic `index.json` manifest.

## Law obligations

We encode algebraic laws for core primitives as small SMT-LIB v2 obligations. Use the CLI to emit either standalone axioms or flow equivalence checks:

```bash
node scripts/emit-smt-laws.mjs --law idempotent:hash -o out/0.4/proofs/laws/idempotent_hash.smt2
node scripts/emit-smt-laws.mjs --equiv examples/flows/info_roundtrip.tf examples/flows/info_roundtrip.tf \
  --laws idempotent:hash,inverse:serialize-deserialize \
  -o out/0.4/proofs/laws/roundtrip_equiv.smt2
node scripts/emit-smt-laws-suite.mjs -o out/0.4/proofs/laws
```

The suite helper emits the canonical set of obligations, including:

- **Hash idempotency** – repeated hashing collapses to a single call.
- **Emit metric commutation** – pure transforms commute with metric emission.
- **Write idempotency by key** – writing the same `(URI, Key, IdKey)` twice equals a single write.
- **Serialize/deserialize round-trips** – `serialize ∘ deserialize` and `deserialize ∘ serialize` act as identities over `Val` and `Bytes`.

The generated files assert the relevant axioms, compare symbolic outputs, and end with `(check-sat)`. CI does not invoke an SMT solver—these files are produced for human review and audit trails alongside our Alloy exports.

Current obligations are structural over uninterpreted functions and deliberately ignore primitive arguments. They justify algebraic rewrites (idempotency, inverse, commutation) rather than semantic equality of parameterized calls. We plan to model arguments later—likely by indexing symbols—but that work is outside D2’s scope.

See also the [SMT emitter](../scripts/emit-smt.mjs) and [Alloy exporter](../scripts/emit-alloy.mjs) for the broader proof pipeline.

## Authorize dominance Alloy model

The `Authorize` checker now ships a structural Alloy encoding that highlights missing or mismatched scope coverage. Generate the
model with:

```bash
node scripts/emit-alloy-auth.mjs examples/flows/auth_missing.tf -o out/0.4/proofs/auth/missing.als
node scripts/emit-alloy-auth.mjs examples/flows/auth_ok.tf      -o out/0.4/proofs/auth/ok.als
```

The exporter maps `authorize(scope="...") { ... }` regions to Alloy `Region` nodes annotated with scopes, while protected
primitives pull their required scopes from `packages/tf-l0-check/rules/authorize-scopes.json`. The resulting module defines
`MissingAuth` and `Covered` predicates plus paired `run` commands to surface counterexamples.

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

`node scripts/proofs-emit-all.mjs` (or `pnpm run proofs:emit`) wraps the individual commands and also emits the law/property SMT bundles listed above.

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

- **Workflow**: L0 Proof Artifacts
- **Artifact name**: `l0-proofs`
- **Files**: Alloy encodings (`*.als`), SMT structural encodings (`*.smt2`), the `laws/` and `props/` folders, and `index.json`

Download from the PR checks page by expanding **L0 Proof Artifacts**, opening **Artifacts**, and grabbing `l0-proofs.zip`. CI does not invoke Alloy or Z3; run `z3 -smt2 <file>` locally or open the `.als` models in Alloy Analyzer if solver output is needed.
