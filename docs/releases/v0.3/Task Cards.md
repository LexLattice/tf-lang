# 0.3 Task Cards — Concept→Code Alignment (TF-Lang)

> Theme: From intent to implementation, verifiably aligned — usable on a real crypto‑bot pilot.

This backlog is designed for agent coders to **self‑unpack** implementation details. Each card is framed conceptually with crisp acceptance criteria, dependencies, and agent prompts.

---

## How to use these cards
- **Work order:** Follow numerical order within each track; tracks can proceed in parallel where dependencies allow.
- **Definition of Done (DoD):** All acceptance criteria met, docs/examples updated, tests green in CI, and a short demo included.
- **Agent prompts:** Copy/paste under each card to bootstrap your plan & sub‑tasks.

---

## Template (for any new card)
- **Intent:** What this enables at the concept→code boundary.
- **Why it matters:** How it contributes to 0.3’s end‑goal and the crypto‑bot pilot.
- **Inputs:** Specs, prior artifacts, or constraints.
- **Deliverables:** Artifacts to produce.
- **Acceptance Criteria:** Verifiable checks.
- **Dependencies:** Cards and/or repos needed first.
- **Agent Prompt (self‑unpack):** Starter prompt for autonomous planning.

---

# Track T1 — Spec & Oracles (Intent Layer)

### T1.1 — `tf-spec` minimal schema (Goals, Invariants, Gates, Lenses, Effects/State)
- **Intent:** Make intent first‑class and executable.
- **Why it matters:** Everything (planning, checking, tracing) hangs off a stable intent schema.
- **Inputs:** Existing TF primitives; language interop needs (TS/Rust).
- **Deliverables:** `schema/tf-spec.schema.json` + docs + 3 example specs.
- **Acceptance Criteria:**
  - JSON schema validates examples.
  - Schema lint in pre‑commit.
  - Round‑trip parse/serialize in TS/Rust adapters.
- **Dependencies:** —
- **Agent Prompt:** “Design a minimal yet extensible `tf-spec` JSON schema covering goals, invariants, gates, lenses, effects/state. Provide 3 examples and round‑trip parsers in TS/Rust.”

### T1.2 — Oracle stdlib: scaffolding & contracts
- **Intent:** Standard predicates that evaluate `tf-spec` invariants on runtime traces/states.
- **Why it matters:** Shared correctness language across designs and runtimes.
- **Inputs:** T1.1 schema; runtime trace format (T3 track).
- **Deliverables:** `oracles/core` package with interfaces + stubs.
- **Acceptance Criteria:**
  - Oracles are pure, deterministic, and side‑effect free.
  - Common result type with explainable failures (machine + human JSON/markdown).
- **Dependencies:** T1.1, partial T3.1 trace shape.
- **Agent Prompt:** “Create an oracle interface, result type with explanations, and register mechanism. Ship stubbed oracles with unit tests.”

### T1.3 — Determinism oracle
- **Intent:** Same inputs + seed ⇒ identical final state and key checkpoints.
- **Why it matters:** Enables replay, parity (TS/Rust), and auditability.
- **Inputs:** Seeded PRNG contract; canonicalization rules.
- **Deliverables:** Oracle implementation + property tests.
- **Acceptance Criteria:**
  - Fails on any nondeterministic float/time/IO usage.
  - Mutation tests demonstrate detection.
- **Dependencies:** T1.2, T2.2 adapters, T3.2 trace capture.
- **Agent Prompt:** “Implement determinism oracle with configurable checkpoints; add mutation tests to prove sensitivity.”

### T1.4 — Conservation oracle (accounting invariants)
- **Intent:** Assets/balances conserved modulo declared effects (fees, fills).
- **Why it matters:** Core safety for the crypto‑bot ledger.
- **Inputs:** Effect schemas from `tf-spec`.
- **Deliverables:** Oracle + fixtures.
- **Acceptance Criteria:** Detects leakage/orphan deltas; clear diff output.
- **Dependencies:** T1.2.
- **Agent Prompt:** “Implement conservation checks over before/after state + effect stream; report mismatched sums and culprits.”

### T1.5 — Idempotence oracle (effects)
- **Intent:** Reapplying effects doesn’t change state after first application.
- **Why it matters:** Retries & exactly‑once semantics.
- **Inputs:** Effect models; lens merge rules.
- **Deliverables:** Oracle + randomized property tests.
- **Acceptance Criteria:** Fails when side effects double‑apply.
- **Dependencies:** T1.2, T3.3 lens rules.
- **Agent Prompt:** “Model replay with duplicate effects; verify no state drift given declared idempotent effects.”

### T1.6 — Transport/Region oracle (lens safety)
- **Intent:** Lenses read/write within declared regions; merges respect boundaries.
- **Why it matters:** Prevents accidental cross‑region corruption.
- **Inputs:** Lens region declarations.
- **Deliverables:** Oracle + region visualizer.
- **Acceptance Criteria:** Violations show exact path and offending op.
- **Dependencies:** T1.2, T3.3.
- **Agent Prompt:** “Validate each lens op against region declarations; emit path‑level diagnostics.”

### T1.7 — Conservativity oracle (CALL gate)
- **Intent:** External calls can only emit allowed effects/schemas.
- **Why it matters:** Enforces boundaries with untrusted adapters.
- **Inputs:** Gate declarations; effect schemas.
- **Deliverables:** Oracle + call‑graph inspection.
- **Acceptance Criteria:** Flags any extra/undeclared effect.
- **Dependencies:** T1.2, T3.1 trace tags.
- **Agent Prompt:** “Check every gate invocation against declared output schema; produce call‑site evidence.”

### T1.8 — Oracle harness: property‑based testing
- **Intent:** Stress oracles with randomized, seeded inputs.
- **Why it matters:** Confidence and regression coverage.
- **Inputs:** Oracles T1.3–T1.7.
- **Deliverables:** TS/Rust harnesses with seeds and shrinkers.
- **Acceptance Criteria:** Reproducible seeds; CI time budget < 5 min.
- **Dependencies:** T1.2.
- **Agent Prompt:** “Build a property‑based harness that runs all oracles under seed sets; emit seed corpus on failures.”

### T1.9 — Oracle strength via mutation tests
- **Intent:** Prove oracles catch realistic faults.
- **Why it matters:** Avoid false confidence.
- **Inputs:** Minimal crypto‑bot models (T5).
- **Deliverables:** Mutation scripts; coverage matrix.
- **Acceptance Criteria:** Kill‑rate ≥ 80% for targeted mutants.
- **Dependencies:** T1.3–T1.8, T5 skeleton.
- **Agent Prompt:** “Inject controlled mutants; report which oracles caught them; improve weak spots.”

---

# Track T2 — Alignment Tooling (Dev/CI Layer)

### T2.1 — `tf-check` CLI skeleton
- **Intent:** One command to run oracles on a project.
- **Why it matters:** Makes alignment frictionless.
- **Inputs:** T1 oracles; T3 traces.
- **Deliverables:** CLI with subcommands (`run`, `report`, `ci`).
- **Acceptance Criteria:** Exit codes map to pass/fail; machine JSON + human summary.
- **Dependencies:** T1.2, T3.1.
- **Agent Prompt:** “Scaffold `tf-check` CLI; plug in oracle registry; produce JSON + pretty console output.”

### T2.2 — Language adapters (TS & Rust)
- **Intent:** Uniform adapter API for running systems under test and collecting traces.
- **Why it matters:** Parity across runtimes.
- **Inputs:** Adapter interface; build tools.
- **Deliverables:** `adapters/ts`, `adapters/rust` with examples.
- **Acceptance Criteria:** Run same spec/oracles on both runtimes from CLI.
- **Dependencies:** T2.1, T3.1.
- **Agent Prompt:** “Implement adapters that compile/run targets, inject seeds, and surface traces to `tf-check`.”

### T2.3 — Concept↔Code annotations & mapper
- **Intent:** Bind code units to `tf-spec` intents (IDs) via macros/decorators.
- **Why it matters:** Generates coverage matrix and reviewer context.
- **Inputs:** T1.1 IDs; language macro systems.
- **Deliverables:** `#[tf(id="...")]` (Rust), `@tf("...")` (TS) + mapper.
- **Acceptance Criteria:** Matrix lists intents ↔ code paths; % covered.
- **Dependencies:** T1.1, T2.2.
- **Agent Prompt:** “Ship annotations and a mapper that builds an intent↔implementation matrix from static & runtime info.”

### T2.4 — Coverage report (JSON→HTML)
- **Intent:** Human‑readable alignment report with links to traces.
- **Why it matters:** PR review clarity.
- **Inputs:** T2.3 matrix + oracle results.
- **Deliverables:** Static HTML generator.
- **Acceptance Criteria:** Drill‑down pages per intent/oracle; artifact saved in CI.
- **Dependencies:** T2.1–T2.3.
- **Agent Prompt:** “Generate an HTML report from JSON results; include filters and deep links to failing traces.”

### T2.5 — GitHub Action integration
- **Intent:** Block merges on misalignment; attach artifacts.
- **Why it matters:** Enforces the standard.
- **Inputs:** T2.1–T2.4.
- **Deliverables:** `.github/workflows/tf-check.yml` + caching.
- **Acceptance Criteria:** PR status checks + uploaded HTML artifacts.
- **Dependencies:** T2.4.
- **Agent Prompt:** “Wire `tf-check` into CI with matrix runs (TS/Rust); cache deps; publish reports.”

---

# Track T3 — Observability & Parity (Trace Layer)

### T3.1 — Proof tags: types & emission points
- **Intent:** Structured trace events: Witness, Normalization, Transport, Refutation, Conservativity.
- **Why it matters:** Reviewer can *follow the proof* of alignment.
- **Inputs:** Tag schema; performance constraints.
- **Deliverables:** Tag structs/enums; emitters at key ops.
- **Acceptance Criteria:** Tags appear only when enabled; stable schema.
- **Dependencies:** T2.2.
- **Agent Prompt:** “Define tag types and instrument code paths to emit them; include golden‑file tests.”

### T3.2 — DEV_PROOFS toggle & zero‑overhead off‑path
- **Intent:** Make tracing fully optional in prod.
- **Why it matters:** No performance regression.
- **Inputs:** Build flags/env vars; benchmarks.
- **Deliverables:** Toggle, compile/runtime guards.
- **Acceptance Criteria:** Overhead ≤ 1% when off; perf report.
- **Dependencies:** T3.1.
- **Agent Prompt:** “Implement feature flags and prove near‑zero overhead with benchmarks.”

### T3.3 — Lens merge rules & region filters
- **Intent:** Canonical merge semantics + region scoping.
- **Why it matters:** Consistent state evolution and oracle checks.
- **Inputs:** Lens definitions from `tf-spec`.
- **Deliverables:** Library + tests + diagrams.
- **Acceptance Criteria:** Same behavior TS/Rust on golden cases.
- **Dependencies:** T1.1, T2.2.
- **Agent Prompt:** “Implement canonical lens merge rules; add region filters; verify parity with fixtures.”

### T3.4 — Unified trace sink + filters
- **Intent:** One log sink with filters by region, gate, oracle, tag.
- **Why it matters:** Reviewer ergonomics.
- **Inputs:** T3.1 tags; adapter hooks.
- **Deliverables:** CLI `tf-check trace --filter ...` + JSONL format.
- **Acceptance Criteria:** Filtering works; large runs stream safely.
- **Dependencies:** T2.1, T3.1.
- **Agent Prompt:** “Create a standardized JSONL sink and filtering CLI; include sample sessions.”

### T3.5 — Cross‑runtime parity suite
- **Intent:** Same seeds ⇒ byte‑identical checkpoints across TS/Rust.
- **Why it matters:** Confidence in dual stacks.
- **Inputs:** T2.2 adapters; T3.3 merge rules.
- **Deliverables:** Parity tests + fixtures.
- **Acceptance Criteria:** All checkpoints equal or diff explained.
- **Dependencies:** T2.2, T3.3.
- **Agent Prompt:** “Implement a parity suite that replays seeds and compares checkpoints with crisp diffs.”

---

# Track T4 — Parallel Design Explorer (Planning Layer)

### T4.1 — `tf-plan` branch space enumeration
- **Intent:** Turn `tf-spec` into a set of design branches (options per component).
- **Why it matters:** Explore before you code.
- **Inputs:** T1.1 spec examples.
- **Deliverables:** Planner that emits branch graph + scores.
- **Acceptance Criteria:** Produces at least 3 viable plans with rationale.
- **Dependencies:** T1.1.
- **Agent Prompt:** “Enumerate configurable components and score trade‑offs (complexity, risk, deps) with explainers.”

### T4.2 — PR scaffolder (N branches)
- **Intent:** Spin up parallel branches wired to the same oracles/CI.
- **Why it matters:** Empirical comparison, apples‑to‑apples.
- **Inputs:** T4.1 plan graph; T2.5 CI.
- **Deliverables:** Script/CLI to create N PR skeletons.
- **Acceptance Criteria:** Each PR builds, runs `tf-check`, and attaches reports.
- **Dependencies:** T4.1, T2.5.
- **Agent Prompt:** “Scaffold N branches from plan nodes; ensure oracles and CI are pre‑wired.”

### T4.3 — Merge guidance report
- **Intent:** Summarize oracle outcomes/trade‑offs to pick a winner.
- **Why it matters:** Decision based on proofs, not vibes.
- **Inputs:** T2.4 reports; T4.1 scores.
- **Deliverables:** Aggregated comparison + recommendation.
- **Acceptance Criteria:** Clear rationale; links to artifacts.
- **Dependencies:** T4.2.
- **Agent Prompt:** “Aggregate results across branches; rank and recommend with explicit oracle evidence.”

---

# Track T5 — Crypto‑bot Pilot (End‑to‑End)

### T5.1 — Repo scaffold & module boundaries
- **Intent:** Minimal, clean pilot repo to host the demo.
- **Why it matters:** Concrete proving ground for 0.3.
- **Inputs:** Preferred build tools; mono‑repo or submodules.
- **Deliverables:** Repo with `/marketdata`, `/strategy`, `/risk`, `/execution`, `/accounting` + examples.
- **Acceptance Criteria:** Builds in TS/Rust; skeleton passes lint & basic tests.
- **Dependencies:** — (parallel with T1/T2).
- **Agent Prompt:** “Scaffold the pilot with five modules and hello‑world flows; wire to adapters.”

### T5.2 — MarketData replay (canonicalization)
- **Intent:** Deterministic input stream with seeded slicing.
- **Why it matters:** Repeatable experiments.
- **Inputs:** CSV/JSON tick snapshots; PRNG.
- **Deliverables:** Replay engine + canonicalization rules.
- **Acceptance Criteria:** Same seed ⇒ identical frames; float handling documented.
- **Dependencies:** T5.1, T3.2.
- **Agent Prompt:** “Build a replay engine that emits canonical frames and honors seeds.”

### T5.3 — Strategy variants (2 minimal)
- **Intent:** Create branchable design choices for T4.
- **Why it matters:** Realistic diversity for planner.
- **Inputs:** Simple momentum vs. mean‑reversion.
- **Deliverables:** Two pluggable strategies with same effect schema.
- **Acceptance Criteria:** Both run under `tf-check`; annotated with intent IDs.
- **Dependencies:** T5.1, T2.3.
- **Agent Prompt:** “Implement two strategies with identical outputs; annotate and test under oracles.”

### T5.4 — Risk module (position & drawdown caps)
- **Intent:** Enforce risk invariants expressed in `tf-spec`.
- **Why it matters:** Central to conservation/idempotence checks.
- **Inputs:** Caps & thresholds from spec.
- **Deliverables:** Risk evaluator + effects (reject/trim orders).
- **Acceptance Criteria:** Oracles detect any breach reliably.
- **Dependencies:** T1.4, T2.3.
- **Agent Prompt:** “Implement position/drawdown caps; surface violations; ensure conservation holds.”

### T5.5 — Execution adapter with CALL gate
- **Intent:** Simulated exchange adapter constrained by Conservativity.
- **Why it matters:** Tests the gate/oracle path end‑to‑end.
- **Inputs:** Declared effect schema; latency model.
- **Deliverables:** Paper‑trade adapter + gate check hooks.
- **Acceptance Criteria:** Any undeclared effect is blocked and reported.
- **Dependencies:** T1.7, T2.2.
- **Agent Prompt:** “Build a paper‑execution adapter that only emits declared effects; integrate gate checks.”

### T5.6 — Accounting / ledger lens
- **Intent:** Source of truth for balances, PnL; merges via lenses.
- **Why it matters:** Conservation and transport checks rely on it.
- **Inputs:** Ledger schema; lens rules (T3.3).
- **Deliverables:** Ledger store + lens ops + tests.
- **Acceptance Criteria:** Parity TS/Rust on golden merges.
- **Dependencies:** T3.3.
- **Agent Prompt:** “Implement ledger + lens merges; ensure deterministic outcomes and region safety.”

### T5.7 — End‑to‑end deterministic replay scenario
- **Intent:** Showcase the full loop on a single replay.
- **Why it matters:** Public demo artifact.
- **Inputs:** T5.2–T5.6 modules.
- **Deliverables:** Script/Make target to run replay and generate reports.
- **Acceptance Criteria:** `tf-check` passes; HTML report + traces saved.
- **Dependencies:** T5.2–T5.6, T2.4.
- **Agent Prompt:** “Create `make demo` that runs replay, runs `tf-check`, and outputs artifacts.”

### T5.8 — CI wiring for pilot
- **Intent:** Enforce alignment in the pilot repo.
- **Why it matters:** Demonstrates the standard.
- **Inputs:** T2.5.
- **Deliverables:** CI workflow + cache.
- **Acceptance Criteria:** PRs blocked on failures; artifacts uploaded.
- **Dependencies:** T2.5.
- **Agent Prompt:** “Add CI job that runs `tf-check` on TS/Rust pilots; publish HTML.”

### T5.9 — Demo README + short video/script
- **Intent:** Explain how the loop works, step by step.
- **Why it matters:** Onboarding and evangelism.
- **Inputs:** Screenshots/reports.
- **Deliverables:** README with gifs or CLI transcript.
- **Acceptance Criteria:** New dev can reproduce in <10 minutes.
- **Dependencies:** T5.7–T5.8.
- **Agent Prompt:** “Write a crisp README with steps and expected outputs; include troubleshooting.”

---

# Track T6 — Cross‑Cutting Quality

### T6.1 — Pre‑commit hooks (schema lint, formatting, license)
- **Intent:** Keep repos clean and consistent.
- **Why it matters:** Lowers friction for agents.
- **Deliverables:** `.pre-commit-config.yaml` + scripts.
- **Acceptance Criteria:** Hooks run locally and in CI.
- **Dependencies:** T1.1.
- **Agent Prompt:** “Add hooks for schema lint, code format, and license headers.”

### T6.2 — Seeds & canonicalization rules
- **Intent:** Precise, language‑agnostic seed & float rules.
- **Why it matters:** Determinism.
- **Deliverables:** Spec doc + libs in TS/Rust.
- **Acceptance Criteria:** Identical outputs across runtimes on tricky cases.
- **Dependencies:** T1.3, T3.5.
- **Agent Prompt:** “Define PRNG/float rules and implement helper libs; add edge‑case tests.”

### T6.3 — Security review of gates/transports
- **Intent:** Threat model for CALL gates and transports.
- **Why it matters:** Prevents privilege escalation via effects.
- **Deliverables:** Checklist + automated checks.
- **Acceptance Criteria:** All gates audited; CI includes checks.
- **Dependencies:** T1.7, T5.5.
- **Agent Prompt:** “Write a threat model and automate the top checks; integrate into CI.”

### T6.4 — Performance baseline with proofs off
- **Intent:** Prove near‑zero overhead when tracing disabled.
- **Why it matters:** Production viability.
- **Deliverables:** Bench suite + report.
- **Acceptance Criteria:** ≤1% overhead off‑path; documented.
- **Dependencies:** T3.2, T5 modules.
- **Agent Prompt:** “Benchmark key paths with/without proofs; optimize until ≤1% regression.”

### T6.5 — Cookbook & examples
- **Intent:** Fast path for users to adopt TF‑Lang workflow.
- **Why it matters:** Scale beyond the pilot.
- **Deliverables:** `examples/` with small, focused scenarios.
- **Acceptance Criteria:** Each example runs `tf-check` and passes at least two oracles.
- **Dependencies:** T2.1–T2.4, T1 oracles.
- **Agent Prompt:** “Author 3 examples (mini‑ledger, counter, router) demonstrating oracles and reports.”

### T6.6 — Concept↔Code matrix visualizer
- **Intent:** Visual map from intents to code and oracle coverage.
- **Why it matters:** Review ergonomics and planning feedback loop.
- **Deliverables:** Static HTML/SVG (or d3) view fed by T2.3 JSON.
- **Acceptance Criteria:** Filters by intent/oracle/runtime; exported in CI artifacts.
- **Dependencies:** T2.3, T2.4.
- **Agent Prompt:** “Render a matrix of intents ↔ code with coverage status and links to traces.”

---

## Milestone markers (suggested)
- **M1 (Week 1–2):** T1.1–T1.4, T2.1, T2.2, T5.1–T5.2.
- **M2 (Week 3–4):** T1.5–T1.7, T2.3–T2.4, T3.1–T3.3, T5.3–T5.5.
- **M3 (Week 5–6):** T1.8–T1.9, T2.5, T3.4–T3.5, T4.1–T4.3, T5.6–T5.9, T6.1–T6.6.

---

## Exit criteria for 0.3
- ≥90% of the crypto‑bot pilot flows covered by `tf-spec` intents & oracles.
- TS & Rust pass the same oracle suite with identical final states on replays.
- Proof tags present only when enabled; overhead ≤1% when disabled.
- `tf-check` integrated in CI; PRs blocked on misalignment; HTML coverage and matrix artifacts attached.
- `tf-plan` generates ≥3 viable designs and a merge recommendation backed by oracle results.

