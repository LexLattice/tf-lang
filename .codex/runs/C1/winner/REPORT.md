# REPORT — C1 — Run WIN

## End Goal fulfillment
- EG-1 (Host-lite endpoints): Exposes only **POST /plan** and **POST /apply**.  
  Proof: `packages/host-lite/src/server.ts`
- EG-2 (Idempotency): Repeating identical requests yields byte-identical responses and does not change state.  
  Proof: `packages/host-lite/test/c1.idempotency.test.ts` (two consecutive POSTs)
- EG-3 (Canonical journal): Responses include canonicalized journal entries; stable ordering/bytes.  
  Proof: `packages/host-lite/src/canonical.ts`, `packages/host-lite/test/c1.canonical.test.ts`
- EG-4 (Ephemeral state): All state is in-memory (lost on restart); no external persistence.  
  Proof: absence of fs/network writes; tests: `packages/host-lite/test/c1.ephemeral.test.ts`
- EG-5 (Proof gating): With `DEV_PROOFS=1` → proof tags present; otherwise → absent.  
  Proof: `packages/host-lite/test/c1.proofs-gated.test.ts`

## Blockers honored
- B-1: No kernel/tag-schema changes — unchanged; host is an add-on. ✅
- B-2: No per-call locks on hot paths — none used. ✅
- B-3: No `static mut`/`unsafe` (Rust) — N/A for host; unaffected. ✅
- B-4: No `as any` in TS — none; literal tuples / proper types used. ✅
- B-5: ESM internal imports include `.js` — verified in host package. ✅
- B-6: Parallel-safe tests, no cross-test state bleed — isolated server via `inject`, no global env leaks. ✅
- B-7: Deterministic outputs (canonical bytes & hashes where relevant) — enforced in snapshots/hash asserts. ✅
- B-8: In-memory only; no files/DB — verified by tests and static search. ✅
- B-9: Only `/plan` & `/apply` — enforced by router; no extra routes. ✅
- Note: We corrected a **typo in `.codex/tasks/**/BLOCKERS.yml`** (inherited from `main`) post-run so the blocker-lint passes; **no semantic changes** to rules.

## Lessons / tradeoffs (≤5 bullets)
- Keeping host **in a single package** (`packages/host-lite`) avoids crossing package boundaries and keeps deps tidy.
- Canonicalization centralized in `canonical.ts` reduces drift from L0 semantics.
- Used request **injection** for tests (no open ports) → stable & fast CI.
- Proof gating kept at the boundary → zero overhead when disabled.
- Minimal surface area → simpler future maintenance (C1 is a leaf).

## Bench notes (optional, off-mode)
- flag check: N/A (host piggybacks on existing DEV_PROOFS gate; no extra hot path)
- no-op emit: not applicable here; verified responses avoid allocations when proofs disabled.
