# Ontology Aligner – Operating Rules (stateless)

Goal: For each task in .codex/PLAN-0.2.md, produce a concise **Alignment Brief** that
translates the v0.2 intent (docs/0.2-RATIONALE.md) into **binding constraints, invariants, and test oracles** for that task.

Process (every session is stateless):
1) Read: docs/0.2-RATIONALE.md, .codex/PLAN-0.2.md, .codex/JOURNAL.md.
2) Select the next task (e.g., A3).
3) Emit `.codex/briefs/A3.md` with the template below.
4) If a brief exists, update it only if the rationale or lessons require (note the delta).

## Alignment Brief template (per task)
[TASK-ID] Alignment Brief
Intent (from RATIONALE)
(2–4 bullets tying task to v0.2 goals)

# Derived Constraints (binding)
Inputs / outputs shape (schemas or example JSON)

Normal forms to enforce (delta/effect)

Pointer rules (RFC6901); final state register (r0)

Hashing/canonicalization points (where to apply)

Rejection rules (e.g., E_L0_FLOAT)

# Invariants & Oracles
What must be true post-impl (e.g., TS/Rust hash equality for X)

Negative tests (should fail)

Performance or safety notes (if any)

# Checklist for Coder
 Mirrors TS and Rust

 Uses canonical bytes (no JSON.stringify)

 Final state ends in r0

 JSON Pointers start with "/"

 Effects NF sorted unique

 Proof tags emitted when DEV_PROOFS=1 (if relevant)

# Lessons referenced
(A1, A2, … with 1-line takeaways)


