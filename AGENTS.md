# AGENTS (Codex Router)

Agents must load includes in order: Global → Family → Role.
Precedence: role > family > global. When rules conflict, the more specific wins.

```yaml agent_routing
version: 1
layers:
  - id: "*"
    name: "Global"
    includes:
      - .codex/PLAN-0.2.md
      - .codex/JOURNAL.md
    rules:
      - "Prefer determinism, reproducibility, and auditability."
      - "Minimize diff surface; keep changes test-backed and explainable."
      - "Non-trivial changes must include a short rationale."

  - id: "codex/*"
    name: "Codex family"
    includes: []
    rules:
      - "Coherent multi-file suggestions; keep patches logically atomic."
      - "Summarize impact across code, tests, and tooling."

  - id: "codex/coder"
    name: "Codex role: coder"
    includes:
      - .codex/MASTER-PROMPT.md
      - .codex/PLAN-0.2.md
      - .codex/JOURNAL.md
      # Brief selection:
      #   If TASK is provided (e.g., TASK=A5), load ".codex/briefs/<TASK>.md".
      #   Else: infer from PR title or branch (token like A5, B2, etc.).
    rules:
      - "Implement per brief; if ambiguous, propose a minimal RFC comment first."
      - "Append an entry to .codex/JOURNAL.md (lessons, plan, changes, verification)."

  - id: "codex/ontology-reviewer"
    name: "Codex role: ontology-reviewer"
    includes:
      - .codex/ALIGNER-MASTER.md
      - .codex/PLAN-0.2.md
      - .codex/JOURNAL.md
    rules:
      - "Check concept consistency and intent↔effect drift across spec, vectors, and runners."
      - "Emit/update the task brief under .codex/briefs/<TASK>.md with constraints & oracles."
