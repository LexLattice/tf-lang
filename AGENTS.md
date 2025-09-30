# AGENTS · TF-Lang v0.6 (Canonical)

**Purpose.** Build **conceptual depth as code**: human intent (L3) → L2 catalog pipelines → L1 macros → **immutable L0 formula** (the 4-primitive kernel). Code binds *after* L0.

---

## Roles
- **Designer** – authors L2 pipelines (domain catalog, human-readable).
- **Expander** – compiles L2 → L1 → L0 (macro expansion). Deterministic, no side effects.
- **Prover** – checks effects & capabilities; runs attached *laws*; emits `out/TFREPORT.json`.
- **Runtime** – executes/simulates L0 with in-memory drivers (no real I/O yet).
- **Driverist** – maps sub-kinds to concrete instances later (Kafka/HTTP/KMS).
- **Auditor** – replays traces and verifies they match L0.

> **Truth lives at L0.** L3→L0 is reasoning; L0→L-3 is implementation. L0 must not be hand-edited.

---

## Quality Gates (each change)
1. **Explainability.** L2/L1 diff summarized in ≤3 sentences.
2. **Reproducibility.** L0 DAG is regenerated from macros (no manual edits).
3. **Soundness.** Effects & capabilities **GREEN** (`tf check`).
4. **Laws.** Attached laws pass (e.g., RPC idempotency by `corr`; CRDT merge laws when selected).
5. **Smoke tests only.** Minimal goldens for key paths (avoid heavy loops now).
6. **Docs.** Update docs when public L2 signatures or laws change.

---

## Checkpoint Routine (mandatory)
- **Edit only inside allowed paths.** Scope guard will hard-fail otherwise.
- **Run checkpoint with a stable, staged diff** after each change (the one habit).
- **Act only on failing rules;** re-run until GREEN, then commit.
- **cp1 lockfile exception:** if a task adds a package, run:
  ```bash
  pnpm -w install --lockfile-only   and commit pnpm-lock.yaml in cp1 only. From cp2 onward, lockfile stays frozen.
  ```

agents.md tweak for 0.6 version