# Track B · Engine core (Expander, transforms, keypairs, registry)

## What exists now
- **Expander**: The macro expander (`packages/expander/expand.mjs`) is responsible for converting L2 pipeline YAML files into L0 JSON DAGs. It recognizes a fixed set of macros (e.g., `interaction.request`, `state.merge`) and expands them into sequences of the four kernel primitives (`Transform`, `Publish`, `Subscribe`, `Keypair`). It also includes a pre-processor to handle multi-line macro invocations in YAML.
- **Transform Runner**: The `Transform` primitive is executed by `packages/transform/index.mjs`. It's a pure function that dispatches on `spec.op` and handles operations like hashing (`blake3`), data manipulation (`concat`, `get`), schema validation (`jsonschema.validate`), and CRDT merges (`crdt.gcounter.merge`). It contains deterministic stubs for non-pure operations like model inference and policy evaluation.
- **Keypair Generator**: Key generation is handled in `packages/entropy/keypair.mjs`. It currently supports `Ed25519` and deterministically generates a public key PEM and a stable `key_id` derived from a Blake3 digest. For test stability, it only returns public material.
- **Instance Registry**: The v2 instance registry (`instances/registry.v2.json`) uses a rule-based system to map nodes to concrete backend implementations (e.g., `@HTTP`, `@Memory`). Rules are matched based on a node's `domain` and `channel`.
- **Macro expander** (`packages/expander/expand.mjs`): translates `interaction.*`, `transform.*`, `policy.*`, `state.*`, and `process.*` macros into kernel nodes with domain-aware instance hints.
- **Pipeline tooling**: `scripts/pipeline-expand.mjs` + `scripts/monitor-expand.mjs` wrap the expander for CLI use; both compute effect summaries and enforce kernel-only outputs.
- **Keypair + RPC helpers**: macro expansion injects deterministic Ed25519 keypair nodes, `hash`-based correlation IDs, and reply topics per request.
- **Instance registry v2**: `instances/registry.v2.json` pairs domain/QoS/channel selectors with hints; `annotateInstances` (used by `tf plan-instances`) stamps runtime.instance + domain metadata.
- **Unit coverage**: tests cover registry fallback, QoS arrays, retry/await/time macros, and CRDT merges.

## How to run (10-minute quickstart)
1. **Expand an L2 pipeline to L0 (implicitly invokes the expander)**.
```bash
node tools/tf-lang-cli/index.mjs <some_command_that_expands> examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
```
2. Expand an L2 pipeline after stripping inline `#` comments.
```bash
node scripts/pipeline-expand.mjs examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml out/auto.fnol.fasttrack.v1.l0.json
```
```bash
node scripts/assert-kernel-only.mjs out/auto.fnol.fasttrack.v1.l0.json
```
3. Annotate instances + view hints.
```bash
node tools/tf-lang-cli/index.mjs plan-instances out/auto.fnol.fasttrack.v1.l0.json
```

## Common errors & fixes
| Symptom | Probable cause | Fix |
| --- | --- | --- |
| `Unsupported macro: <macro_name>` | The L2 pipeline YAML uses a macro that is not defined in the `MACROS` constant in `packages/expander/expand.mjs`. | Implement the missing macro handler in the expander or correct the typo in the L2 YAML. |
| `Unsupported transform op: <op_name>` | An L0 file contains a `Transform` node with a `spec.op` that is not handled by the `runTransform` function in `packages/transform/index.mjs`. | Add a case for the new operation in the `runTransform` switch statement. |
| `invalid call syntax … # types | ` indicates the expander still sees inline comments. Preprocess YAML to remove trailing comments or update macros to place type notes on separate lines. | ` indicates the expander still sees inline comments. Preprocess YAML to remove trailing comments or update macros to place type notes on separate lines. |
| Unsupported macros (`Unsupported macro | …`) point to missing handlers in `MACROS`. The quickest patch is adding a stub in `expand.mjs` mirroring existing patterns. | …`) point to missing handlers in `MACROS`. The quickest patch is adding a stub in `expand.mjs` mirroring existing patterns. |
| Instance planning defaults to `@Memory` without registry.v2; ensure `instances/registry.v2.json` exists or pass `--registry`. | Investigate root cause | Document mitigation |

## Acceptance gates & signals
| Gate | Command | Success signal |
| --- | --- | --- |
| **Expand an L2 pipeline to L0 (implicitly invokes the expander)** | `node tools/tf-lang-cli/index.mjs <some_command_that_expands> examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml` | Command succeeds without errors. |
| Expand an L2 pipeline after stripping inline `#` comments | `node scripts/pipeline-expand.mjs examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml out/auto.fnol.fasttrack.v1.l0.json` | Command succeeds without errors. |
| Expand an L2 pipeline after stripping inline `#` comments | `node scripts/assert-kernel-only.mjs out/auto.fnol.fasttrack.v1.l0.json` | Command succeeds without errors. |
| Annotate instances + view hints | `node tools/tf-lang-cli/index.mjs plan-instances out/auto.fnol.fasttrack.v1.l0.json` | Command succeeds without errors. |

## DX gaps
- **Discoverability (Expander)**: The macro expansion logic is a core part of the engine, but there is no direct, documented CLI command to perform L2 to L0 expansion. Developers must find wrapper scripts (`pipeline-expand.mjs`) or infer its usage from tests.
- **Code Clarity (Expander)**: The `preprocessL2Yaml` function in `expand.mjs` uses a fragile, stateful loop with regex to wrap multi-line macros in quotes. This is a common source of parsing errors and is hard to debug. A more robust YAML parsing strategy is needed.
- **Extensibility (Transform Runner)**: The `runTransform` function is a single, large `switch` statement. Adding new operations requires modifying this central file, which can lead to merge conflicts and makes the code harder to maintain. A more modular, pluggable architecture would be better.
- **Documentation (Instance Registry)**: The structure and matching logic of the v2 instance registry are not documented. A contributor would need to read the `resolve.mjs` source to understand how to write rules or what the `default` key means.
- No `tf expand` CLI front-door; contributors must know about bespoke scripts.
- Inline comment intolerance breaks the default examples and discourages adding type annotations in YAML.
- Domain overrides + plan metadata never persisted back into the L0 JSON, so downstream tools repeat inference.

## Top issues (synthesized)
- **Discoverability (Expander)**: The macro expansion logic is a core part of the engine, but there is no direct, documented CLI command to perform L2 to L0 expansion. Developers must find wrapper scripts (`pipeline-expand.mjs`) or infer its usage from tests.
- **Code Clarity (Expander)**: The `preprocessL2Yaml` function in `expand.mjs` uses a fragile, stateful loop with regex to wrap multi-line macros in quotes. This is a common source of parsing errors and is hard to debug. A more robust YAML parsing strategy is needed.
- **Extensibility (Transform Runner)**: The `runTransform` function is a single, large `switch` statement. Adding new operations requires modifying this central file, which can lead to merge conflicts and makes the code harder to maintain. A more modular, pluggable architecture would be better.

## Next 3 improvements
- **Expose a dedicated `tf expand` CLI command** — Action: Add an `expand` command to `tools/tf-lang-cli/index.mjs` that takes an L2 YAML file and outputs the corresponding L0 JSON; Impact: High. Makes a core engine function discoverable and easy to use for local debugging and development; Effort: Small
- **Refactor YAML macro parsing to use standard features** — Action: Remove the `preprocessL2Yaml` string manipulation hack. Instead, document and enforce the use of standard YAML block scalars (`|` or `>`) for multi-line macro invocations; Impact: High. Eliminates a fragile and error-prone part of the system, improving reliability; Effort: Medium
- **Refactor the Transform Runner to be modular** — Action: Change `runTransform` from a large switch statement to a dispatch mechanism that uses a map of registered transform operations. Each op would be its own small function; Impact: Medium. Improves maintainability and makes it easier and safer to add new transform operations; Effort: Medium

## References
- [packages/expander/expand.mjs](../../../../packages/expander/expand.mjs)
- [packages/transform/index.mjs](../../../../packages/transform/index.mjs)
- [packages/entropy/keypair.mjs](../../../../packages/entropy/keypair.mjs)
- [instances/registry.v2.json](../../../../instances/registry.v2.json)
- [tools/tf-lang-cli/index.mjs](../../../../tools/tf-lang-cli/index.mjs)
- [examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml](../../../../examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml)
- [scripts/pipeline-expand.mjs](../../../../scripts/pipeline-expand.mjs)
- [scripts/monitor-expand.mjs](../../../../scripts/monitor-expand.mjs)
- [scripts/assert-kernel-only.mjs](../../../../scripts/assert-kernel-only.mjs)
- [tasks/run-examples.sh](../../../../tasks/run-examples.sh)
