# L0 Proofs

## Law obligations

We emit SMT-LIB obligations for the algebraic laws that back our small-model
proofs. Use `scripts/emit-smt-laws.mjs` to write the axioms for a law or check
that two flows are equivalent under a set of laws:

```bash
node scripts/emit-smt-laws.mjs --law idempotent:hash \
  -o out/0.4/proofs/laws/idempotent_hash.smt2

node scripts/emit-smt-laws.mjs --equiv examples/flows/info_roundtrip.tf \
  examples/flows/info_roundtrip.tf \
  --laws idempotent:hash,inverse:serialize-deserialize \
  -o out/0.4/proofs/laws/roundtrip_equiv.smt2
```

These emitters are deterministic and live alongside the general SMT generator
in [`packages/tf-l0-proofs/src/smt-laws.mjs`](../packages/tf-l0-proofs/src/smt-laws.mjs)
and the Alloy tooling in [`packages/tf-l0-proofs/src/alloy.mjs`](../packages/tf-l0-proofs/src/alloy.mjs).
CI does not run any solvers; generated SMT is reviewed as a human/audit
artifact.
