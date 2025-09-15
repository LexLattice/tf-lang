T1_1_P1 — PR Ranking and Synthesis

Scores (0..5; futureproof 0..3)

- PR #92 (A): goal_fit 4, blockers 5, determinism 5, minimality 5, hygiene 5, futureproof 3 — total 27
- PR #93 (B): goal_fit 3, blockers 5, determinism 5, minimality 5, hygiene 4, futureproof 2 — total 24
- PR #94 (C): goal_fit 5, blockers 5, determinism 5, minimality 5, hygiene 5, futureproof 2 — total 27
- PR #95 (D): goal_fit 5, blockers 5, determinism 5, minimality 5, hygiene 5, futureproof 2 — total 27
- PR #96 (E): goal_fit 5, blockers 5, determinism 5, minimality 5, hygiene 5, futureproof 2 — total 27

Winner

- PR #94 (label C)
- Why over next best: clear, complete mapping to schema + adapters + examples with an explicit tf-spec CI job and dev-only Ajv; evidence links are consistent and align with acceptance. D/E are very close; C’s evidence layout is crisper and matches expected file naming.

Per‑run notes

- A (#92)
  - Mentions minimal schema, docs, 3 examples, TS/Rust adapters.
  - Doesn’t explicitly call out the tf-spec CI job; otherwise strong goal fit.
- B (#93)
  - Evidence lists one example (dimension_eq.json); unclear if ≥3 examples present.
  - “Lean schema without version negotiation” is minimal today but less future‑ready.
- C (#94)
  - Calls out validation script and a dedicated tf-spec CI job; dev‑only Ajv; parity tests in both runtimes.
  - Examples referenced via docs/specs and examples/specs/ directories.
- D (#95)
  - Similar coverage; includes validation script path; test filename variant (spec-adapter.test.ts) but hygiene claims are solid.
- E (#96)
  - Comprehensive summary; explicitly mentions a new CI job and canonical JSON; Rust adapter path uses mod.rs (fine).

Patch plan (winner PR #94)

- Add schema at `schema/tf-spec.schema.json` covering core fields in examples.
- Author `docs/specs/tf-spec.md` with scope, field table, and example links.
- Provide ≥3 validating examples under `examples/specs/` and a CI dev validator (Ajv).
- Implement round‑trip adapters in TS (`packages/tf-lang-l0-ts/src/spec/adapter.ts`) and Rust (`packages/tf-lang-l0-rs/src/spec/adapter.rs`) with canonical JSON output and tests.
- Add CI job `tf-spec` to validate examples and run adapter round‑trip tests; upload `tf-spec/validation.txt` artifact.

