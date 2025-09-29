# TF Lang 0.5 — Top Issues Index

## Track A — LSP Proto & DSL Ergonomics

1. **S2 · C2** — `wrapWithAuthorize` in [`packages/tf-lsp-server/src/actions/wrap-authorize.mjs`](../../packages/tf-lsp-server/src/actions/wrap-authorize.mjs) emits `Authorize{…}` which the DSL parser rejects.
   - **Repro:** `node scripts/lsp-smoke/stdio.mjs --mode codeAction --file samples/a1/protected_write.tf`
   - **Owner:** A1 LSP maintainers
   - **Target (date):** 2024-07-05
2. **S1 · C2** — `tf/sourceMap` handler in [`packages/tf-lsp-server/src/server.ts`](../../packages/tf-lsp-server/src/server.ts) reads arbitrary disk paths without validation.
   - **Repro:** `node -e "import('node:child_process').then(({spawn})=>{const srv=spawn(process.execPath,['packages/tf-lsp-server/bin/server.mjs','--stdio']);const send=s=>srv.stdin.write('Content-Length: '+Buffer.byteLength(s)+'\\r\\n\\r\\n'+s);send('{\\"jsonrpc\\":\\"2.0\\",\\"id\\":1,\\"method\\":\\"initialize\\",\\"params\\":{}}');setTimeout(()=>{send('{\\"jsonrpc\\":\\"2.0\\",\\"id\\":2,\\"method\\":\\"tf/sourceMap\\",\\"params\\":{\\"file\\":\\"/etc/passwd\\"}}');},200);srv.stdout.on('data',d=>process.stdout.write(String(d)));setTimeout(()=>srv.kill(),1200);});"`
   - **Owner:** Security desk (Track A)
   - **Target (date):** 2024-06-28
3. **S3 · C2** — Offset conversion in [`packages/tf-lsp-server/src/server.ts`](../../packages/tf-lsp-server/src/server.ts) rescans the full buffer per hover, yielding O(n²) latency.
   - **Repro:** `node scripts/lsp-smoke/stdio.mjs --mode hover --file samples/a1/illegal_write.tf --symbol "tf:network/publish@1"`
   - **Owner:** A1 LSP maintainers
   - **Target (date):** 2024-07-12
4. **S3 · C2** — `extractFQSymbol` in [`packages/tf-lsp-server/src/server.ts`](../../packages/tf-lsp-server/src/server.ts) splits the whole document on each hover, generating large allocations.
   - **Repro:** `node scripts/lsp-smoke/stdio.mjs --mode hover --file samples/a1/illegal_write.tf --symbol "tf:network/publish@1"`
   - **Owner:** A1 LSP maintainers
   - **Target (date):** 2024-07-12
5. **S3 · C2** — Diagnostics emitted from [`packages/tf-lsp-server/src/server.ts`](../../packages/tf-lsp-server/src/server.ts) pin to document start because IR spans are discarded.
   - **Repro:** `node scripts/lsp-smoke/stdio.mjs --mode diagnostics --file samples/a1/protected_write.tf`
   - **Owner:** A1 LSP maintainers
   - **Target (date):** 2024-07-08
6. **S3 · C2** — String literal escapes in [`packages/tf-compose/src/parser.mjs`](../../packages/tf-compose/src/parser.mjs) remain encoded, so runtime receives the wrong payload.
   - **Repro:** `node packages/tf-compose/bin/tf.mjs parse samples/a4/let_basic.tf -o out/0.45/a4/let.json`
   - **Owner:** A4 DSL maintainers
   - **Target (date):** 2024-07-15
7. **S2 · C2** — `authorize` lexer in [`packages/tf-compose/src/parser.mjs`](../../packages/tf-compose/src/parser.mjs) forbids whitespace before `{`, breaking formatted code.
   - **Repro:** `node packages/tf-compose/bin/tf.mjs parse samples/a1/protected_write.tf`
   - **Owner:** A4 DSL maintainers
   - **Target (date):** 2024-06-28
8. **S3 · C2** — `computeInlineLetActions` in [`packages/tf-lsp-server/src/server.ts`](../../packages/tf-lsp-server/src/server.ts) truncates multi-line `let` initialisers.
   - **Repro:** `node scripts/lsp-smoke/stdio.mjs --mode codeAction --file samples/a4/dup_expr.tf --grep "Inline let"`
   - **Owner:** A4 DSL maintainers
   - **Target (date):** 2024-07-19
9. **S4 · C2** — `findOccurrences` regex in [`packages/tf-lsp-server/src/server.ts`](../../packages/tf-lsp-server/src/server.ts) lacks Unicode support, skipping non-ASCII identifiers.
   - **Repro:** `node scripts/lsp-smoke/stdio.mjs --mode codeAction --file samples/a4/let_decl.tf --select "idént"`
   - **Owner:** A1 LSP maintainers
   - **Target (date):** 2024-07-26
10. **S4 · C1** — Hover fallback in [`packages/tf-lsp-server/src/server.ts`](../../packages/tf-lsp-server/src/server.ts) omits array signatures when metadata lacks `input.object`.
    - **Repro:** `node scripts/lsp-smoke/stdio.mjs --mode hover --file samples/a4/let_decl.tf --position 6:2`
    - **Owner:** A1 LSP maintainers
    - **Target (date):** 2024-07-26

## Track B — Runtime

1. **S2 · C2** — `updateTraceIdsFromWasm` in [`packages/tf-run-wasm/src/index.ts`](../../packages/tf-run-wasm/src/index.ts) splits string payloads into characters.
   - **Repro:** `node packages/tf-run-wasm/bin/cli.mjs --ir out/0.4/ir/signing.ir.json --trace out/0.5/wasm/trace.jsonl --status out/0.5/wasm/status.json`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-07-05
2. **S2 · C2** — `enumerateComponentPlans` in [`packages/tf-plan-enum/src/index.ts`](../../packages/tf-plan-enum/src/index.ts) calls `forEach` on `undefined` for unknown ops.
   - **Repro:** `node --input-type=module -e "import('../../packages/tf-plan-enum/src/index.js').then(m=>{const spec={name:'spec',steps:[{op:'migrate_db'}]};try{m.enumeratePlan(spec,{});}catch(err){console.error(err.message);process.exit(1);}});"`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-07-12
3. **S3 · C2** — CLI in [`packages/tf-run-wasm/src/index.ts`](../../packages/tf-run-wasm/src/index.ts) attempts `readFile('undefined')` when no IR source is supplied.
   - **Repro:** `node packages/tf-run-wasm/bin/cli.mjs --trace-path out/0.5/wasm/trace.jsonl`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-07-19
4. **S3 · C1** — `ensureParentDirectory` in [`packages/tf-run-wasm/src/index.ts`](../../packages/tf-run-wasm/src/index.ts) mishandles trailing slashes.
   - **Repro:** `node packages/tf-run-wasm/bin/cli.mjs --trace out/trace/ --ir out/0.4/ir/signing.ir.json`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-07-19
5. **S3 · C2** — `updateTraceIdsFromWasm` trusts unbounded arrays from WASM, risking OOM.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && node - <<"NODE"
const fs=require("fs");
const path="out/0.5/repro/huge-trace.jsonl";
fs.writeFileSync(path,"{\"trace_ids\":[\""+"x".repeat(100000)+"\"]}\n");
NODE
node packages/tf-run-wasm/bin/cli.mjs --ir out/0.4/ir/signing.ir.json --trace out/0.5/repro/huge-trace.jsonl --status out/0.5/repro/status.json'`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-07-26
6. **S3 · C2** — `rescorePlan` in [`packages/tf-plan/src/index.ts`](../../packages/tf-plan/src/index.ts) silently drops missing dependency IDs.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/missing-deps.plan.json
{"nodes":{},"branches":[{"deps":["missing"],"score":{"total":1,"complexity":0,"risk":0,"perf":0,"devTime":0,"depsReady":0}}]}
JSON
node packages/tf-plan/dist/cli.js score --plan out/0.5/repro/missing-deps.plan.json --out out/0.5/repro/missing-deps.scored.json'`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-07-12
7. **S4 · C2** — `writeNdjson` in [`packages/tf-plan/src/index.ts`](../../packages/tf-plan/src/index.ts) writes giant buffers at once.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && node - <<"NODE"
const fs=require("fs");
const nodes={};
for(let i=0;i<100000;i++){nodes["n"+i]={id:"n"+i,score:{total:1}};}
const plan={nodes,branches:[]};
fs.writeFileSync("out/0.5/repro/big.plan.json",JSON.stringify(plan));
NODE
node packages/tf-plan/dist/cli.js export --plan out/0.5/repro/big.plan.json --ndjson out/0.5/repro/big.ndjson'`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-08-02
8. **S3 · C1** — `enumerateBranches` in [`packages/tf-plan-enum/src/index.ts`](../../packages/tf-plan-enum/src/index.ts) treats `--beam-width 0` as success.
   - **Repro:** `node --input-type=module -e "import('../../packages/tf-plan-enum/src/index.js').then(m=>{const spec={name:'beam',steps:[{op:'copy'}]};try{m.enumeratePlan(spec,{beamWidth:0});}catch(err){console.error(err.message);process.exit(1);}});"`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-07-26
9. **S4 · C2** — `aggregateScore` in [`packages/tf-plan-enum/src/index.ts`](../../packages/tf-plan-enum/src/index.ts) double-normalises totals.
   - **Repro:** `node --input-type=module -e "import('../../packages/tf-plan-enum/src/index.js').then(m=>{const nodes=[{component:'a',choice:'x',score:{total:1,complexity:0,risk:0,perf:0,devTime:0,depsReady:0,explain:[]},nodeId:'a'},{component:'b',choice:'y',score:{total:3,complexity:0,risk:0,perf:0,devTime:0,depsReady:0,explain:[]},nodeId:'b'}];console.log(m.aggregateScore(nodes));});"`
   - **Owner:** Runtime maintainers (B1/B2)
   - **Target (date):** 2024-08-02
10. **S4 · C1** — `readSpec` in [`packages/tf-plan-enum/src/index.ts`](../../packages/tf-plan-enum/src/index.ts) loads massive specs entirely in memory.
    - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && python - <<"PY"
import json
spec={"steps":[{"op":"noop","args":{}} for _ in range(200000)]}
with open("out/0.5/repro/huge.spec.json","w") as fh:
    json.dump(spec,fh)
PY
node packages/tf-plan/dist/cli.js enumerate --spec out/0.5/repro/huge.spec.json --out out/0.5/repro/huge-plan'`
    - **Owner:** Runtime maintainers (B1/B2)
    - **Target (date):** 2024-08-09

## Track C — Trace & Perf

1. **S3 · C2** — `ingestTraceFile` in [`packages/tf-trace/src/lib/ingest.ts`](../../packages/tf-trace/src/lib/ingest.ts) reads entire traces into memory.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && python - <<"PY"
import json
with open("out/0.5/repro/trace_large.jsonl","w") as fh:
    for i in range(500000):
        fh.write(json.dumps({"ts":i,"prim_id":"p","effect":"Network.Out"})+"\n")
PY
node packages/tf-trace/bin/trace.mjs validate --in out/0.5/repro/trace_large.jsonl'`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-07-12
2. **S3 · C2** — Blank lines skipped in [`packages/tf-trace/src/lib/ingest.ts`](../../packages/tf-trace/src/lib/ingest.ts) hide ingestion gaps.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"EOF" > out/0.5/repro/trace_blank_line.jsonl
{"ts":1,"prim_id":"p","effect":"Network.Out"}

{"ts":2,"prim_id":"p","effect":"Network.Out"}
EOF
node packages/tf-trace/bin/trace.mjs validate --in out/0.5/repro/trace_blank_line.jsonl'`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-07-05
3. **S2 · C2** — `validateTraceRecord` in [`packages/tf-trace/src/lib/validate.ts`](../../packages/tf-trace/src/lib/validate.ts) rejects optional metadata fields.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/trace-extra.jsonl
{"ts":1,"prim_id":"p","effect":"e","id":"x"}
JSON
node packages/tf-trace/bin/trace.mjs validate --in out/0.5/repro/trace-extra.jsonl'`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-06-28
4. **S3 · C1** — `validateBudgetSpecShape` in [`packages/tf-trace/bin/trace.mjs`](../../packages/tf-trace/bin/trace.mjs) allows non-finite thresholds.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/budget-invalid.json
{"effect":"Network.Out","count_max":0,"ms_max":null}
JSON
node packages/tf-trace/bin/trace.mjs budget --in samples/c/trace_small.jsonl --spec out/0.5/repro/budget-invalid.json'`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-07-12
5. **S3 · C2** — `evaluateBudget` in [`packages/tf-trace/src/lib/budget.ts`](../../packages/tf-trace/src/lib/budget.ts) omits declared-but-absent effects from reasons.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/budget-missing.json
{"budgets":[{"effect":"EffectX","count_max":0}]}
JSON
node packages/tf-trace/bin/trace.mjs budget --in samples/c/trace_small.jsonl --spec out/0.5/repro/budget-missing.json'`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-07-19
6. **S3 · C2** — Summary totals in [`packages/tf-trace/src/lib/summary.ts`](../../packages/tf-trace/src/lib/summary.ts) expose float precision noise.
   - **Repro:** `node packages/tf-trace/bin/trace.mjs summary --in samples/c/trace_small.jsonl --out out/0.5/trace/summary.json`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-07-19
7. **S4 · C2** — `buildTraceCSV` in [`packages/tf-trace/bin/trace.mjs`](../../packages/tf-trace/bin/trace.mjs) concatenates rows into one giant string.
   - **Repro:** `node packages/tf-trace/bin/trace.mjs export --in out/0.5/repro/trace_large.jsonl --csv out/0.5/trace/trace.csv`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-08-02
8. **S4 · C1** — CSV export header checks in [`packages/tf-trace/bin/trace.mjs`](../../packages/tf-trace/bin/trace.mjs) rely on substring matching.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cp samples/c/trace_small.jsonl out/0.5/repro/trace_small.jsonl && node packages/tf-trace/bin/trace.mjs summary --in out/0.5/repro/trace_small.jsonl --out out/0.5/repro/summary.json && sed -i "s/prim_id/prim_identifier/" out/0.5/repro/summary.json && node packages/tf-trace/bin/trace.mjs export --summary out/0.5/repro/summary.json --csv out/0.5/repro/summary.csv'`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-08-02
9. **S4 · C2** — Budget CLI in [`packages/tf-trace/bin/trace.mjs`](../../packages/tf-trace/bin/trace.mjs) documents `--format text` but returns an error.
   - **Repro:** `node packages/tf-trace/bin/trace.mjs summary --in samples/c/trace_small.jsonl --format text`
   - **Owner:** Trace tooling team
   - **Target (date):** 2024-07-26
10. **S3 · C1** — No perf gate quick mode; CLI lacks `--limit` to bound ingestion work.
    - **Repro:** `node packages/tf-trace/bin/trace.mjs summary --in out/0.5/repro/trace_large.jsonl`
    - **Owner:** Trace tooling team
    - **Target (date):** 2024-07-26

## Track D — Optimizer

1. **S2 · C2** — `applyInverseOnce` in [`packages/tf-opt/lib/plan-apply.mjs`](../../packages/tf-opt/lib/plan-apply.mjs) removes mismatched codec pairs.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/codec-mismatch.ir.json
{"nodes":[{"prim":"serialize_json"},{"prim":"deserialize_binary"}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/codec-mismatch.ir.json -o out/0.5/repro/codec.plan.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-05
2. **S2 · C2** — `applyCommuteOnce` ignores obligation directionality.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/commute-direction.ir.json
{"obligations":[{"kind":"commute","direction":"right","left":"emit","right":"pure"}],"nodes":[{"prim":"emit"},{"prim":"pure"}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/commute-direction.ir.json -o out/0.5/repro/commute.plan.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-05
3. **S3 · C2** — `cloneIr` falls back to JSON clone, losing metadata.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/annotated.ir.json
{"nodes":[{"prim":"noop","loc":{"line":1}}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/annotated.ir.json -o out/0.5/repro/annotated.plan.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-12
4. **S3 · C1** — `applyCommuteOnce` mutates arrays in place, skipping later swaps.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/commute-chain.ir.json
{"nodes":[{"prim":"emit_metric"},{"prim":"pure"},{"prim":"emit_metric"}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/commute-chain.ir.json -o out/0.5/repro/commute-chain.plan.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-12
5. **S3 · C2** — `extractPrimitivesFromIr` misses nested primitives in [`packages/tf-opt/lib/rewrite-detect.mjs`](../../packages/tf-opt/lib/rewrite-detect.mjs).
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/nested-prim.ir.json
{"nodes":[{"prim":"compose","args":{"inner":{"prim":"serialize"}}}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/nested-prim.ir.json --emit-used-laws out/0.5/repro/nested-laws.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-19
6. **S3 · C2** — `analyzePrimitiveSequence` builds commute obligations without effect metadata.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/missing-effect.ir.json
{"nodes":[{"prim":"unknown_op"},{"prim":"pure"}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/missing-effect.ir.json --emit-used-laws out/0.5/repro/missing-effect-laws.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-19
7. **S3 · C1** — Idempotent detection uses strict equality including metadata.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/idempotent-metadata.ir.json
{"nodes":[{"prim":"hash","loc":{"file":"a"}},{"prim":"hash","loc":{"file":"b"}}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/idempotent-metadata.ir.json -o out/0.5/repro/idempotent.plan.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-26
8. **S4 · C2** — Rewrite loop lacks iteration cap, risking infinite toggles.
   - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/oscillate.ir.json
{"nodes":[{"prim":"swap_a"},{"prim":"swap_b"}],"obligations":[{"kind":"commute","left":"swap_a","right":"swap_b"},{"kind":"commute","left":"swap_b","right":"swap_a"}]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/oscillate.ir.json -o out/0.5/repro/oscillate.plan.json'`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-07-26
9. **S4 · C2** — `loadPrimitiveEffectMap` caches catalog forever in [`packages/tf-opt/lib/data.mjs`](../../packages/tf-opt/lib/data.mjs).
   - **Repro:** `node packages/tf-opt/bin/opt.mjs --cost show`
   - **Owner:** Optimizer maintainers (D1/D2)
   - **Target (date):** 2024-08-02
10. **S4 · C1** — `canonicalLawName` misses case normalisation in [`packages/tf-opt/lib/data.mjs`](../../packages/tf-opt/lib/data.mjs).
    - **Repro:** `bash -lc 'mkdir -p out/0.5/repro && cat <<"JSON" > out/0.5/repro/case-law.ir.json
{"laws":["Idempotent:Hash"]}
JSON
node packages/tf-opt/bin/opt.mjs --ir out/0.5/repro/case-law.ir.json --emit-used-laws out/0.5/repro/case-law-laws.json'`
    - **Owner:** Optimizer maintainers (D1/D2)
    - **Target (date):** 2024-08-09

## Track E — Proofs

1. **S2 · C2** — `emitFlowEquivalence` lacks definition for `write-by-key` in [`packages/tf-l0-proofs/src/smt-laws.mjs`](../../packages/tf-l0-proofs/src/smt-laws.mjs).
   - **Repro:** `node scripts/proofs/ci-gate.mjs --emit-law idempotent:write-by-key`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-07-05
2. **S1 · C2** — `idempotent:write-by-key` law encodes a satisfiable negation, producing false proofs.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --law idempotent:write-by-key --z3 $(command -v z3)`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-06-28
3. **S2 · C2** — `normalizeLawList` preserves caller casing, conflicting with canonical names.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --emit-law Idempotent:Hash`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-07-05
4. **S3 · C2** — `normalizeOperation` fails to strip namespace prefixes.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --emit-law tf:network/publish@1`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-07-12
5. **S3 · C1** — `emitFlowEquivalence` emits duplicate function declarations.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --emit-laws idempotent:hash,commute:hash`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-07-19
6. **S3 · C2** — Flow arity mismatches throw before solver inspection.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --emit-laws commute:left-right`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-07-19
7. **S3 · C1** — `collectSorts` throws late on typos, aborting whole runs.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --emit-law typo:missing`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-07-26
8. **S4 · C2** — `listLawNames` relies on object insertion order, causing nondeterministic listings.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --list-laws`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-08-02
9. **S4 · C1** — `emitLaw` omits `(get-model)` for failing proofs, limiting debugging.
   - **Repro:** `node scripts/proofs/ci-gate.mjs --law idempotent:write-by-key --z3 $(command -v z3)`
   - **Owner:** Proofs maintainers (E1/E2)
   - **Target (date):** 2024-08-02
10. **S4 · C1** — Lack of automated unsat tests leaves SMT regressions undetected.
    - **Repro:** `node scripts/proofs/ci-gate.mjs --law smoke`
    - **Owner:** Proofs maintainers (E1/E2)
    - **Target (date):** 2024-08-09

## Track F — DevEx & Release

1. **S3 · C2** — `pack-all` timestamp in [`tools/release/pack-all.mjs`](../../tools/release/pack-all.mjs) breaks determinism.
   - **Repro:** `node tools/release/pack-all.mjs`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-07-05
2. **S3 · C2** — `scripts/docs/build.mjs` embeds timestamps, making docs non-repeatable.
   - **Repro:** `node scripts/docs/build.mjs`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-07-05
3. **S3 · C1** — `pack-all` outputs unsorted package manifests.
   - **Repro:** `node tools/release/pack-all.mjs --roots packages/a,packages/b`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-07-12
4. **S4 · C2** — `tools/ci/lockfile-guard.mjs` ignores `--json` flag semantics.
   - **Repro:** `node tools/ci/lockfile-guard.mjs --json`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-07-26
5. **S3 · C1** — `pack-all` fails to re-check `private` post-pack, risking accidental publish.
   - **Repro:** `node tools/release/pack-all.mjs`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-07-19
6. **S3 · C2** — `pack-all` allows heavy `prepack` hooks to run during dry runs.
   - **Repro:** `node tools/release/pack-all.mjs`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-07-26
7. **S3 · C1** — `.github/workflows/release.yml` only exercises Ubuntu Node 20.
   - **Repro:** `cat .github/workflows/release.yml`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-08-02
8. **S4 · C2** — `setup-pnpm` composite always reinstalls packages when `install: true`.
   - **Repro:** `node -e "console.log(require('fs').readFileSync('.github/actions/setup-pnpm/action.yml','utf8'))"`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-08-02
9. **S4 · C1** — Docs and lockfile guard duplicate CLI scaffolding, leading to drift.
   - **Repro:** `node scripts/docs/build.mjs && node tools/ci/lockfile-guard.mjs`
   - **Owner:** DevEx & release maintainers
   - **Target (date):** 2024-08-09
10. **S3 · C2** — `pack-all` hashes the manifest instead of built tarballs, missing integrity coverage.
    - **Repro:** `node tools/release/pack-all.mjs`
    - **Owner:** DevEx & release maintainers
    - **Target (date):** 2024-08-09
