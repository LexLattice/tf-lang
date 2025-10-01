# Track H · Prover deepening

## What exists now
- **Solver bindings** (`packages/prover/z3.mjs`): lazy-loads `z3-solver` and exposes `proveStableCorrImpliesIdempotent` + `proveGuardExclusive` helpers.
- **Counterexample finder** (`packages/prover/counterexample.mjs`): enumerates boolean assignments (≤8 vars) and reports triggered rule IDs for branch overlaps or max-bound exceedance.
- **Law suite integration** (`laws/*.mjs`): idempotency uses Z3 implication proof; branch exclusivity funnels through prover guards; monotonic log + confidential envelope report PASS/WARN heuristics.
- **CLI access**: `tf laws --check` surfaces branch exclusivity/monotonic/confidential results with `--max-bools` and optional JSON output.

## How to run
```bash
# Branch exclusivity search with tighter bound
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive --max-bools 4

# Machine-readable payload (includes WARN/ERROR metadata)
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive --json
```
Inspect output for `WARN` (e.g., confidential envelope plaintext) or `max-bools-exceeded` sentinel when guard space too large.

## Common errors + fixes
- `solver-init-missing` arises when `z3-solver` optional dep is not installed; rerun `pnpm install --frozen-lockfile` and ensure Node 20.
- Large guard sets trigger `max-bools-exceeded`; lower branching by splitting conditionals or increase bound (capped at 8).
- `predicate-required` from `findCounterexample` indicates a law handler invoked prover without predicate; file an issue—the CLI should never expose it.

## Gaps
- No CLI exposes counterexample JSON directly; branch exclusivity NEUTRAL gives no insight into guard coverage.
- Confidential envelope + monotonic log rely on heuristics, not solver-backed proofs; WARNs never fail builds, weakening compliance story.
- No docs describing how to author custom law goals or interpret prover payloads.

## Next 3 improvements
1. Add `tf laws --counterexample` flag to dump assignments + triggered branches for failed exclusivity proofs.
2. Extend prover hooks for policy dominance (Authorize monotonicity) and confidential envelope (ciphertext vs plaintext) with concrete counterexamples.
3. Document law goal semantics + sample outputs in `docs/0.6/laws.md`, including how `max-bools` interacts with nested guards.
