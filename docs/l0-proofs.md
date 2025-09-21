# L0 Proofs

## Law obligations

Law proofs are emitted as SMT-LIB obligations under small bounded domains. Use the SMT emitter to materialize the axioms and specific flow-equivalence checks:

```bash
# Emit axioms for a single law
node scripts/emit-smt-laws.mjs --law idempotent:hash -o out/0.4/proofs/laws/idempotent_hash.smt2

# Emit equivalence checks for concrete flows with their governing laws
node scripts/emit-smt-laws.mjs --equiv examples/flows/info_roundtrip.tf examples/flows/info_roundtrip.tf \
  --laws idempotent:hash,inverse:serialize-deserialize \
  -o out/0.4/proofs/laws/roundtrip_equiv.smt2
```

CI does not invoke an SMT solver; emitted files are for human or audit review. See the SMT emitter and Alloy sections for broader proof tooling.
