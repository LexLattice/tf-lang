# Track E · L1 macros & laws

## What exists now
- **Macro catalog** (`packages/expander/expand.mjs` + `catalog/*.json`): supports `interaction.receive/request/reply`, `transform.validate/model_infer/compose/lookup`, `policy.evaluate/enforce/record_decision`, `state.diff/merge/jsonpatch/crdt`, `process.retry/await.any/await.all/timeout/saga/schedule`, and `obs.emit_metric`.
- **Law metadata** (`packages/expander/catalog/state.merge.json`, `docs/0.6/index.md`): documents jsonpatch (order-sensitive) vs CRDT G-counter (associative/commutative/idempotent).
- **Checker wiring**: idempotency uses Z3 to prove `hasCorr && corrStable ⇒ idempotent`; CRDT merge + confidential envelope + monotonic log implemented as deterministic heuristics.
- **Tests**: `packages/expander/tests/state.macros.test.mjs` and `process.macros.test.mjs` cover merge strategies, retries, and schedule expansion.

## How to run
```bash
# Expand a state.merge example (no inline comments)
node scripts/pipeline-expand.mjs packages/expander/tests/fixtures/state.merge.l2.yaml out/state.merge.l0.json

# Law inspection
node tools/tf-lang-cli/index.mjs laws --check out/state.merge.l0.json --goal branch-exclusive --json
```

## Common errors + fixes
- `state.merge: unsupported strategy` → allowed values are `jsonpatch` and `crdt.gcounter`. Default is jsonpatch when omitted; document this in authoring guides.
- `process.retry` requires the nested step to emit stable corr IDs; otherwise checker reports `unstable-corr`. Pair retries with transforms that hash deterministic payload slices.
- Macro authorship is brittle: trailing comments or YAML anchors are not sanitized; keep macro lines simple or preprocess before expansion.

## Gaps
- No macro reference doc for `policy.enforce`, `process.saga`, or `state.diff`; teams must read source to understand inputs/outputs.
- Law suite lacks coverage for policy dominance, saga monotonicity, or `process.await` exclusivity.
- CRDT/jsonpatch notes live in code comments; docs do not surface example payloads or invariants.

## Next 3 improvements
1. Generate `docs/0.6/macros/*.md` from catalog metadata (inputs, outputs, law assumptions) so designers can author L2 without reading JS.
2. Extend law harness with counterexamples for `process.await.any/all` (branch exclusivity) and `policy.enforce` (deny path monotonicity).
3. Provide macro authoring lint (pre-commit) to fail on inline comments/anchors that the expander cannot parse, keeping source consistent.
