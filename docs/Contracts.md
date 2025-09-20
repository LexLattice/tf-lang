# Contracts & Normative Changes

**Normative** (requires version bump & review):
- ID policy changes, DSL grammar, IR node set, trace envelope
- Primitive contracts: effects, footprints, qos, errors, data_classes
- Checker semantics (Par/Seq rules, dominance)

**Tweak** (safe to batch at phase integration):
- Refactors, test/data additions, adapter ergonomics, docs polish

Use `npm run contracts:check-breaking` to enforce rules against `contracts/baseline/*`.
