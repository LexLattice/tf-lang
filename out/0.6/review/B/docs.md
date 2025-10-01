# Track B · Engine core (Expander, transforms, keypairs, registry)

## What exists now
- **Macro expander** (`packages/expander/expand.mjs`): translates `interaction.*`, `transform.*`, `policy.*`, `state.*`, and `process.*` macros into kernel nodes with domain-aware instance hints.
- **Pipeline tooling**: `scripts/pipeline-expand.mjs` + `scripts/monitor-expand.mjs` wrap the expander for CLI use; both compute effect summaries and enforce kernel-only outputs.
- **Keypair + RPC helpers**: macro expansion injects deterministic Ed25519 keypair nodes, `hash`-based correlation IDs, and reply topics per request.
- **Instance registry v2**: `instances/registry.v2.json` pairs domain/QoS/channel selectors with hints; `annotateInstances` (used by `tf plan-instances`) stamps runtime.instance + domain metadata.
- **Unit coverage**: tests cover registry fallback, QoS arrays, retry/await/time macros, and CRDT merges.

## How to run
1. Expand an L2 pipeline after stripping inline `#` comments:
   ```bash
   node scripts/pipeline-expand.mjs examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml out/auto.fnol.fasttrack.v1.l0.json
   node scripts/assert-kernel-only.mjs out/auto.fnol.fasttrack.v1.l0.json
   ```
2. Annotate instances + view hints:
   ```bash
   node tools/tf-lang-cli/index.mjs plan-instances out/auto.fnol.fasttrack.v1.l0.json
   ```
3. Review effects + DOT to confirm expansion fidelity.

## Common errors + fixes
- `invalid call syntax … # types:` indicates the expander still sees inline comments. Preprocess YAML to remove trailing comments or update macros to place type notes on separate lines.
- Unsupported macros (`Unsupported macro: …`) point to missing handlers in `MACROS`. The quickest patch is adding a stub in `expand.mjs` mirroring existing patterns.
- Instance planning defaults to `@Memory` without registry.v2; ensure `instances/registry.v2.json` exists or pass `--registry`.

## Gaps
- No `tf expand` CLI front-door; contributors must know about bespoke scripts.
- Inline comment intolerance breaks the default examples and discourages adding type annotations in YAML.
- Domain overrides + plan metadata never persisted back into the L0 JSON, so downstream tools repeat inference.

## Next 3 improvements
1. Expose `tf expand <L2> --out <L0>` leveraging `packages/expander/expand.mjs` with comment-stripping preprocessor baked in.
2. Persist instance annotations + effect summary into the emitted L0 (today `tasks/run-examples.sh` recomputes effects separately).
3. Extend macro handlers to surface expansion notes (e.g., `process.saga`, `state.merge`) in generated docs so 0.6 law coverage is auditable from artifacts.
