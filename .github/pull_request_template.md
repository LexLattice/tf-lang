<!-- Auto-filled by AGENT:CODER. Keep it concise and factual. -->

# {{TASK_ID}} — Pass {{PASS}} — Run {{RUN_LABEL}}

## Summary (≤ 3 bullets)
- What changed and why (implementation, not tests)
- What you intentionally did NOT change (scope guard)
- Any tradeoff worth noting

## End Goal → Evidence
- EG-1: <code/test link>
- EG-2: <…>

## Blockers honored (must all be ✅)
- B-1: ✅ <code link>
- B-2: ✅ <code link>

## Determinism & Hygiene
- Byte-identical outputs across repeats: ✅
- SQL-only / no JS slicing (if applicable): ✅
- ESM `.js`, no deep imports, no `as any`: ✅

## Self-review checklist (must be all ✅)
- [ ] Production code changed (tests only ≠ pass)
- [ ] Inputs validated; 4xx on bad shapes
- [ ] No new runtime deps (unless allowed)
- [ ] CI gauntlet green

## Delta since previous pass (≤ 5 bullets)
- …
