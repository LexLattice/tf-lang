# Architecture Decision Record (ADR)

&gt; One-liners; newest at top. Keep decisions factual, tied to tasks/passes.

- **2025-09-13 · ADR-0003 · C1 finalized** — Host-lite exports `src/server.ts` (no dist), DI `makeRawHandler` → canonical **400/404**, unified `exec(world, plan)` for `/plan` & `/apply`, per-world **LRU(32)**, proofs strictly behind `DEV_PROOFS=1`, ESM internals use **`.js`**, no deep imports, hermetic tests.
- **2025-09-12 · ADR-0002 · Planner briefs** — Tasks use the **END_GOAL + BLOCKERS + ACCEPTANCE** format under `.codex/tasks/&lt;ID&gt;/`.
- **2025-09-11 · ADR-0001 · Agent role** — Single **CODER** role in `.codex/agents.md`; only active when explicitly invoked.
