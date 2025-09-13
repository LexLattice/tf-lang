# Architecture Decision Record (ADR)

&gt; One-liners; newest at top. Keep decisions factual, tied to tasks/passes.
- **2025-09-13 · ADR-0004 · D1 finalized** — Legal adapter uses **SQLite via sql.js (WASM)** built in-memory from schema/seed fixtures; all queries **parameterized** (hot ones **prepared & reused**); **SQL-only** filtering/paging with **ORDER BY**; responses include `dataset_version` and **BLAKE3(canonical_request_bytes)** as `query_hash`; return **≥10 distinct** evidence items; ESM internals use **`.js`**; no DB binaries tracked; tests hermetic & parallel-safe with byte-identical determinism.
- **2025-09-13 · ADR-0003 · C1 finalized** — Host-lite exports `src/server.ts` (no dist), DI `makeRawHandler` → canonical **400/404**, unified `exec(world, plan)` for `/plan` & `/apply`, per-world **LRU(32)**, proofs strictly behind `DEV_PROOFS=1`, ESM internals use **`.js`**, no deep imports, hermetic tests.
- **2025-09-12 · ADR-0002 · Planner briefs** — Tasks use the **END_GOAL + BLOCKERS + ACCEPTANCE** format under `.codex/tasks/&lt;ID&gt;/`.
- **2025-09-11 · ADR-0001 · Agent role** — Single **CODER** role in `.codex/agents.md`; only active when explicitly invoked.
