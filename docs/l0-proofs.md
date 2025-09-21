# L0 Proofs

## Law obligations

We generate SMT-LIB artefacts for algebraic laws via the `scripts/emit-smt-laws.mjs` helper.
Use `--law` to write standalone axioms and `--equiv` with `--laws` to compare two
flow fragments under a set of assumptions. These commands only emit obligations for
human or offline solver review; CI never attempts to discharge them.

```
node scripts/emit-smt-laws.mjs --law idempotent:hash -o out/0.4/proofs/laws/idempotent_hash.smt2
node scripts/emit-smt-laws.mjs --equiv examples/flows/info_roundtrip.tf examples/flows/info_roundtrip.tf \
  --laws idempotent:hash,inverse:serialize-deserialize -o out/0.4/proofs/laws/roundtrip_equiv.smt2
```

See also the Alloy and SMT emitters for related modelling flows.
