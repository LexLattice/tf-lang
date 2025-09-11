# AGENTS (routing + phases; project specifics live in .codex)

**Precedence:** Custom instructions > this file > repo files.  
**Roles:** codex/coder, codex/ontology-reviewer.  
**Always:** no binaries; keep patches minimal & test-backed.

## Files to consult (if present)
- `.codex/LESSONS.md`      ← always read; compact rules
- `.codex/PLAN-*.md`       ← optional plan; pick latest version
- `.codex/briefs/<TASK>.md`← task brief selected via TASK token or PR/branch title
- `.codex/JOURNAL.md`      ← append-only; do not reread each task
- `.codex/self-plans/<TASK>.md` ← phase 1 output
- `.codex/polish/<TASK>.md`     ← phase 3 output

## 4-phase loop (auto-advance; MAX_POLISH=1)
1) **Plan (architect):** write `.codex/self-plans/<TASK>.md` with steps, tests, risks, DoD. No edits.  
2) **Implement (coder):** apply plan; update/add tests; append one A7 entry to `JOURNAL.md`; add ≤1 new bullet to `LESSONS.md` only if a general rule emerged.  
3) **Polish (ontology reviewer):** review **current PR diff only**; write `.codex/polish/<TASK>.md` with minimal, safe improvements.  
4) **Apply polish (coder):** implement polish notes; keep diff tiny. Stop after one polish pass.

## TASK selection
- If `TASK=<token>` is provided, use it. Else infer from PR title/branch (e.g., `A7`). If none, abort and ask for TASK.

## Guardrails
- Integer-only semantics; assertions/probes **fail hard** (no `null` on invalid).  
- RFC6901 pointers; invalid traversal → `null` where stated by runner spec; effects in normalized form (sorted, unique).  
- Do **not** change CI workflows unless explicitly asked.

