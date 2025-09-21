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
