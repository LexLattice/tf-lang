# T1_1 — Intent Schema (tf-spec)

1) Provide a JSON Schema at `schema/tf-spec.schema.json` that defines the core intent format.
   - *Why:* Everything (plan/check/trace) builds on a stable, validated schema.

2) Author documentation explaining the schema and its fields, with at least three minimal, real examples.
   - *Why:* Makes the format legible and reviewable; anchors future extensions.

3) Include three example specs under `examples/specs/` that validate against the schema.
   - *Why:* Executable samples serve as oracles and onboarding material.

4) Implement **round-trip adapters** (parse → canonical → serialize) in **TypeScript** and **Rust** for the subset covered by the examples.
   - *Why:* Proves cross-runtime parity and prevents “schema drift” between implementations.
