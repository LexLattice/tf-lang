# Track C · Runtime & Checker

## What exists now
- **Deterministic runtime core** (`packages/runtime/run.mjs`): in-memory bus, transform evaluator covering JSON schema validation, hashing, CRDT merges, policy eval, auth token mint/check, time alignment, saga planning.
- **Checker CLI** (`packages/checker/check.mjs`): evaluates declared vs computed effects, policy allowlists, capability lattice requirements, RPC pairing, idempotency via Z3, CRDT merge coverage, monotonic log + confidential envelope heuristics.
- **`tf laws --check`**: friendly wrapper for branch exclusivity/monotonic/confidential goals with JSON or console output.
- **Monitoring utilities**: `scripts/assert-kernel-only.mjs` and example spec scripts assert RPC pairing, PII guardrails, effect summaries for monitors.

## How to run
```bash
# Full checker report
node packages/checker/check.mjs \
  examples/v0.6/build/auto.quote.bind.issue.v2.l0.json \
  --policy policy/policy.allow.json \
  --caps policy/policy.allow.json \
  --out out/quote.bind.issue.report.json

# Lightweight law scan (branch exclusivity / monotonic / confidential)
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.quote.bind.issue.v2.l0.json --max-bools 4
```
Inspect `out/*.json` for RED/AMBER gates; the checker is deterministic (sorted arrays, ISO timestamp).

## Common errors + fixes
- **Missing capability manifest** → checker status RED even when policy passes. Fix by pointing `--caps` to an allowlist JSON (same shape as `policy.allow.json`) or generate `out/caps.json` listing granted caps.
- **Idempotency RED** on RPC publishes stems from macros that hash entropy-bearing bodies without stable seeds. For demos mark as known gap; long-term fix is to ensure `corr` derives from deterministic inputs or wrap in `process.retry` with saga key.
- **Z3 optional dep**: first solver call downloads a wasm; ensure `pnpm install` succeeded. If offline, expect `solver-failed` reasons — document as WARN, not blocker.

## Gaps
- No runtime harness to execute L0 pipelines against the memory bus; only checker + specs exist.
- Checker lacks per-rule exit codes (always exit 0), so CI integration must parse JSON manually.
- Law coverage is shallow: branch exclusivity/monotonic/confidential only produce PASS/NEUTRAL; no counterexample emission wired into CLI output.

## Next 3 improvements
1. Ship `tf check` alias that wraps `packages/checker/check.mjs` with defaults + non-zero exit when `status !== GREEN` for release gating.
2. Add a minimal executor CLI (`tf run --l0 … --caps …`) to replay a flow on the deterministic bus for smoke testing.
3. Thread counterexample payloads from `findCounterexample` into `tf laws --check --json`, enabling teams to triage branch overlaps locally.
