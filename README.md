# TF-Lang (v0.3) — True Functions, Oracles & Deterministic Pilot

[CI: T4 Plan/Scaffold/Compare](.github/workflows/t4-plan-scaffold-compare.yml)
[CI: T3 Trace & Perf](.github/workflows/t3-trace-and-perf.yml)
Version: v0.3

[![Pages](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml/badge.svg?branch=main)](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml)
**Live site:** https://LexLattice.github.io/tf-lang/

## What’s in 0.3
- T3 — Observability & Parity:
  - Proof tags & `DEV_PROOFS` gating; `tf-check trace --filter …` JSONL stream.
  - TS↔Rust parity harness; perf harness for proofs-off path.
- T4 — Parallel Design Explorer:
  - `tf-plan` enumerate; `tf-plan-compare` merge recommendation report; CI pipeline.
- T5 — Pilot (TS path): Replay → Strategy (momentum/mean-reversion) → Risk (exposure).
  - Deterministic artifacts, seeded runs, and reproducible hashes.

## Quickstart
### A) Standard developer setup
```bash
pnpm -v && node -v
pnpm -w -r install
pnpm -w -r build
```

### B) Codex Cloud setup (one-liner)

```bash
bash -lc "./scripts/codex/setup.sh"
```

### Policy checks

Policy check:
`node packages/tf-compose/bin/tf-policy.mjs check examples/flows/txn_ok.tf`
Use `--forbid-outside` to reject writes outside transactions, and `--catalog <path>` to supply a catalog; otherwise the CLI falls back to name-based detection with a warning.

## Generated pipeline adapters

TypeScript emissions now include a minimal adapter surface under `runtime/adapters/types.ts`.
The generated `src/adapters.ts` file re-exports this surface and augments it with strongly
typed entry points for every primitive that appears in the flow.

For deterministic local runs, use the in-memory factory published at
`runtime/adapters/inmem.mjs`. It implements storage writes with idempotency keys,
compare-and-swap semantics, publish/metric aggregation, and HMAC-SHA256 crypto helpers.
All adapters are pure Node.js implementations and require no external services.

**Safety:** Generated runners *fail fast* if a required adapter method is missing
(e.g., `writeObject`, `publish`, `emitMetric`, `sign`, `verify`, `hash`). Supply
adapters explicitly or use the bundled `runtime/adapters/inmem.mjs` for deterministic local runs.

## Determinism & Proofs (T3)

* Turn proofs on only when tracing:

```bash
DEV_PROOFS=1 node packages/tf-check/dist/cli.js trace \
  --runtime ts --limit 50 \
  --out out/t3/trace/ts.jsonl --filter tag=Transport
head -n 3 out/t3/trace/ts.jsonl | jq -c .
```
```json
{"runtime":"ts","ts":1758319451311,"region":"/acct","oracle":"Transport","seed":0,"tag":{"kind":"Transport","op":"LENS_PROJ","region":"/acct/0"}}
{"runtime":"ts","ts":1758319451314,"region":"/acct","oracle":"Transport","seed":1,"tag":{"kind":"Transport","op":"LENS_PROJ","region":"/acct/1"}}
{"runtime":"ts","ts":1758319451314,"region":"/acct","oracle":"Transport","seed":2,"tag":{"kind":"Transport","op":"LENS_PROJ","region":"/acct/2"}}
```

* Parity & perf (paths listed; run on demand).

## T4 — Plan → Compare (demo)

```bash
node packages/tf-plan/dist/cli.js enumerate \
  --spec tests/specs/demo.json --seed 42 --beam 3 --out out/t4/plan
# optional compare if inputs exist
node packages/tf-plan-compare/dist/cli.js compare \
  --plan out/t4/plan/plan.ndjson \
  --inputs out/t4/scaffold/index.json \
  --out out/t4/compare
```

* Outputs:

  * `out/t4/plan/plan.json`, `out/t4/plan/plan.ndjson`
  * (if present) `out/t4/compare/{report.json, report.md, index.html}`

## T5 — Pilot (Replay → Strategy → Risk)

* **Deterministic run** (safe then force):

```bash
pnpm run t5:run  || true    # safe: fails if artifacts exist
pnpm run t5:rerun           # force: overwrites artifacts
cat out/t5/status.json      # lines & sha256 per file
```

* Example (captured from your run):

  * seed: `42`, slice: `0:50:1`
  * frames: **12** lines, sha256: `2a9ed33962d71dd3b2c25cd37db84a09d28fa08d762a7b11b7ebc2d99011bc89`
  * orders: **8** lines, sha256: `81f44de9b15fa7b9c5b631375857765f134f5560051cf7565d353d556449fdc5`
  * evaluations: **1** lines, sha256: `580478ac3d9fa9befc20bcc735f9aaffc841f55eb1d49fbd82f`

## Repository Map

```
packages/
  tf-check/                 # trace CLI (T3.4)
  tf-plan/ tf-plan-compare/ # T4 planner & compare
  pilot-core/ replay/ strategy/ risk/  # T5 pilot stack
scripts/
  codex/ setup.sh maint.sh
  t5-run.mjs t5-write-status.js
out/ (artifacts)/
```

## CI

* Workflows:

  * T4 Plan/Scaffold/Compare: `.github/workflows/t4-plan-scaffold-compare.yml`
  * T3 Perf/Trace: `.github/workflows/t3-trace-and-perf.yml`
* PRs upload artifacts under `out/**`.

## What’s next (0.4)

* Trace Explorer (static, safe UI).
* WASM & Python bindings (parity with Rust/TS).
* Streaming scale (1M–10M frames) and perf suite.
* Plugin SDK + config schema.
* Release pipeline (packages, SBOMs, checksums).

## Contributing

* PRs must produce deterministic artifacts (same seed ⇒ same hashes).
* No `shell:true`, no `eval`; CRLF-safe file readers (`/\r?\n/`).

## License 

* MIT

```
## Meta-Ontology 0.4 — Hard-Ground Starter

This repo skeleton grounds A0 → B4 so builders can flesh out implementations without
arguing about structure. It includes: IDs & versions, catalog ingest, effects/laws stubs,
DSL+IR+canonicalizer, checker glue, and TS/Rust codegen skeletons.

### Quick Start

```bash
# Node 20+ recommended (see ./toolchain/.node-version)
npm ci

# A0: IDs & Versions (deterministic)
npm run a0

# A1: Catalog ingest + effects/laws skeleton
npm run a1

# Parse, check, and canon an example flow
npm run tf -- parse examples/flows/signing.tf -o out/0.4/ir/signing.ir.json
npm run tf -- check examples/flows/signing.tf -o out/0.4/flows/signing.verdict.json
npm run tf -- canon examples/flows/signing.tf -o out/0.4/ir/signing.canon.json

# Generate Rust scaffold for the flow
node scripts/generate-rs.mjs out/0.4/ir/signing.ir.json -o out/0.4/codegen-rs/signing
# (optional) LOCAL_RUST=1 cargo build -Z unstable-options --manifest-path out/0.4/codegen-rs/signing/Cargo.toml

# Generate TS skeleton for the flow
npm run tf -- emit --lang ts examples/flows/signing.tf --out out/0.4/codegen-ts/signing

# Run generated code with capability enforcement (+ env fallback)
# caps.json: {"effects":["Storage.Write","Pure","Observability"],"allow_writes_prefixes":["res://kv/"]}
npm run tf -- emit --lang ts examples/flows/run_storage_ok.tf --out out/0.4/codegen-ts/run_storage_ok
node out/0.4/codegen-ts/run_storage_ok/run.mjs --caps caps.json
TF_CAPS='{"effects":["Network.Out","Pure"],"allow_writes_prefixes":[]}' node out/0.4/codegen-ts/run_publish/run.mjs
# Summarize traces
cat tests/fixtures/trace-sample.jsonl | node packages/tf-l0-tools/trace-summary.mjs --top=3 --pretty

### Trace files (T3)
- Runners always print JSON trace lines to stdout; setting `TF_TRACE_PATH=out/0.4/traces/<name>.jsonl` is an optional mirror.
- Per run: `TF_TRACE_PATH=out/0.4/traces/publish.jsonl node out/0.4/codegen-ts/run_publish/run.mjs --caps caps.json`.
- Multi-run append: reuse the same `TF_TRACE_PATH` for later invocations (even in one process) and each call appends more JSON.
- Records follow `schemas/trace.v0.4.schema.json`, so existing tooling keeps working.
- Validate: `cat file.jsonl | node scripts/validate-trace.mjs`.
- Provenance check:
  ```bash
  TF_PROVENANCE=1 node scripts/pilot-build-run.mjs
  node scripts/validate-trace.mjs --require-meta \
    --ir $(jq -r .provenance.ir_hash out/0.4/pilot-l0/status.json) \
    --manifest $(jq -r .provenance.manifest_hash out/0.4/pilot-l0/status.json) \
    --catalog $(jq -r .provenance.catalog_hash out/0.4/pilot-l0/status.json) \
    < out/0.4/pilot-l0/trace.jsonl
  node packages/tf-compose/bin/tf-verify-trace.mjs \
    --ir out/0.4/pilot-l0/pilot_min.ir.json \
    --manifest out/0.4/pilot-l0/pilot_min.manifest.json \
    --status out/0.4/pilot-l0/status.json \
    --trace out/0.4/pilot-l0/trace.jsonl
  ```

See [docs/l0-proofs.md](docs/l0-proofs.md) for generating SMT/Alloy proofs and downloading the CI artifacts emitted for v0.4 flows.

### Example App: Order Publish
```bash
node scripts/app-order-publish.mjs
cat out/0.4/apps/order_publish/summary.json
# pass --pretty to the script if you want pretty-printed stdout
# node scripts/app-order-publish.mjs --pretty
```
The script emits `examples/flows/app_order_publish.tf` into `out/0.4/apps/order_publish`.
It writes `out/0.4/apps/order_publish/caps.json` with `{"effects":["Network.Out","Observability","Pure"],"allow_writes_prefixes":[]}`.
The generated runner enforces those capabilities through its embedded manifest before using the in-memory runtime.
The resulting trace summary reports publish primitives and effects so you can audit the capability-gated execution.

# Generate capability manifest
node packages/tf-compose/bin/tf-manifest.mjs examples/flows/manifest_publish.tf
node packages/tf-compose/bin/tf-manifest.mjs examples/flows/manifest_storage.tf -o out/0.4/manifests/storage.json
# Manifests print to stdout or land under out/0.4/manifests/

# Filter trace JSONL streams
cat out/t3/trace/ts.jsonl | node packages/tf-l0-tools/trace-filter.mjs --effect=Network.Out --grep=orders --pretty
cat tests/fixtures/trace-sample.jsonl | node packages/tf-l0-tools/trace-filter.mjs --prim=tf:resource/write-object@1
Tip: malformed lines are skipped with a warning; pass --quiet to suppress it.
```

### Tree
- `catalogs/` — legacy YAMLs (frontend_primitives.yaml, information_primitives.yaml, interaction_interface.yaml, observability_telemetry.yaml, policy_governance.yaml, process_computation.yaml, resource_infrastructure.yaml, security_primitives.yaml, state_identity.yaml)
- `packages/`
  - `tf-l0-spec/` — A0/A1: IDs, versions, catalog ingest, effects/laws scaffolding
  - `tf-l0-ir/` — IR schema, codecs, canonicalizer
  - `tf-l0-check/` — effect lattice, footprints, checker glue
  - `tf-compose/` — CLI: parse/check/canon/emit/manifest
  - `tf-l0-codegen-ts/` — TS emitter (skeleton)
  - `tf-l0-codegen-rs/` — Rust emitter (skeleton)
- `schemas/` — shared JSON Schemas (trace, manifest, catalog, etc.)
- `examples/flows/` — sample DSL flows
- `docs/` — DSL cheatsheet, catalog doc, traces, etc.
- `out/0.4/` — artifacts

### Determinism
- Canonical JSON writer with stable key order included.
- Hashes (`sha256`) generated for core artifacts.
