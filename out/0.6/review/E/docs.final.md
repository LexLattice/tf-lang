# Track E · L1 macros & laws

## What exists now
- **Macro Definitions**: A suite of L1 macros for state, process, and policy are defined in `packages/expander/expand.mjs`. These include: `state.snapshot`, `state.version`, `state.diff`, `state.merge` `process.retry`, `process.await.any`, `process.await.all`, `process.timeout`, `process.saga` `policy.evaluate`, `policy.enforce`
- **Law Attachment**: The `state.merge` macro demonstrates how algebraic laws are attached to L0 nodes. When the `strategy` is `crdt.gcounter`, it explicitly adds `associative`, `commutative`, and `idempotent` law IDs to the `Transform` node's metadata. For `jsonpatch`, it correctly notes the absence of such laws.
- **Law Modules**: The `laws/` directory contains modules for checking specific properties, such as `crdt-merge.mjs` and `idempotency.mjs`.
- **Authentication Ops**: Low-level authentication operations (`auth.mint_token`, `auth.check_token`) are implemented as pure functions in `packages/ops/auth.mjs` and exposed as `Transform` ops in `packages/transform/index.mjs`.
- **Macro catalog** (`packages/expander/expand.mjs` + `catalog/*.json`): supports `interaction.receive/request/reply`, `transform.validate/model_infer/compose/lookup`, `policy.evaluate/enforce/record_decision`, `state.diff/merge/jsonpatch/crdt`, `process.retry/await.any/await.all/timeout/saga/schedule`, and `obs.emit_metric`.
- **Law metadata** (`packages/expander/catalog/state.merge.json`, `docs/0.6/index.md`): documents jsonpatch (order-sensitive) vs CRDT G-counter (associative/commutative/idempotent).
- **Checker wiring**: idempotency uses Z3 to prove `hasCorr && corrStable ⇒ idempotent`; CRDT merge + confidential envelope + monotonic log implemented as deterministic heuristics.
- **Tests**: `packages/expander/tests/state.macros.test.mjs` and `process.macros.test.mjs` cover merge strategies, retries, and schedule expansion.

## How to run (10-minute quickstart)
1. **Using a macro**: Define it in an L2 pipeline YAML file. The expander processes it automatically.
```bash
steps:
```
```bash
- merge_state: state.merge(strategy: "crdt.gcounter", base: "@...", patch: "@...")
```
2. **Checking laws**: The tf-checker (`packages/checker/check.mjs`) orchestrates law verification, but the implementation is incomplete. The `crdt-merge.mjs` law, for instance, runs a static set of hardcoded samples and does not dynamically check the L0 file.
```bash
tf-checker
```
3. Run command.
```bash
node scripts/pipeline-expand.mjs packages/expander/tests/fixtures/state.merge.l2.yaml out/state.merge.l0.json
```
```bash
node tools/tf-lang-cli/index.mjs laws --check out/state.merge.l0.json --goal branch-exclusive --json
```

## Common errors & fixes
| Symptom | Probable cause | Fix |
| --- | --- | --- |
| `state.merge: unsupported strategy <STRATEGY>` | Using an unknown strategy (e.g., `lww`) in the `state.merge` macro. | Implement the new strategy in the `expandStateMerge` function in `packages/expander/expand.mjs` and add a corresponding transform op. |
| Logical Error (Not a Crash)** | The system correctly identifies that `jsonpatch` has no algebraic laws, but there is no gate to prevent its misuse in parallel execution paths. | This is a design-time issue. The developer must ensure that order-sensitive operations are correctly sequenced in the L2 pipeline. The tool does not automatically prevent this class of error. |
| `state.merge | unsupported strategy` → allowed values are `jsonpatch` and `crdt.gcounter`. Default is jsonpatch when omitted; document this in authoring guides. | unsupported strategy` → allowed values are `jsonpatch` and `crdt.gcounter`. Default is jsonpatch when omitted; document this in authoring guides. |
| `process.retry` requires the nested step to emit stable corr IDs; otherwise checker reports `unstable-corr`. Pair retries with transforms that hash deterministic payload slices. | Investigate root cause | Document mitigation |
| Macro authorship is brittle | trailing comments or YAML anchors are not sanitized; keep macro lines simple or preprocess before expansion. | trailing comments or YAML anchors are not sanitized; keep macro lines simple or preprocess before expansion. |

## Acceptance gates & signals
| Gate | Command | Success signal |
| --- | --- | --- |
| **Using a macro**: Define it in an L2 pipeline YAML file. The expander processes it automatically | `steps:` | Command succeeds without errors. |
| **Using a macro**: Define it in an L2 pipeline YAML file. The expander processes it automatically | `- merge_state: state.merge(strategy: "crdt.gcounter", base: "@...", patch: "@...")` | Command succeeds without errors. |
| **Checking laws**: The tf-checker (`packages/checker/check.mjs`) orchestrates law verification, but the implementation is incomplete. The `crdt-merge.mjs` law, for instance, runs a static set of hardcoded samples and does not dynamically check the L0 file | `tf-checker` | Command succeeds without errors. |
| Run command | `node scripts/pipeline-expand.mjs packages/expander/tests/fixtures/state.merge.l2.yaml out/state.merge.l0.json` | Command succeeds without errors. |
| Run command | `node tools/tf-lang-cli/index.mjs laws --check out/state.merge.l0.json --goal branch-exclusive --json` | Command succeeds without errors. |

## DX gaps
- **Release Blocker (Disconnected Law Checking)**: The law verification system is fundamentally flawed. The `state.merge` macro attaches law IDs to L0 nodes, but the corresponding law checker (`laws/crdt-merge.mjs`) **does not read or use them**. Instead, it runs a few hardcoded, static examples. This creates a dangerous illusion of verification; the system is not actually checking the algebraic properties of the code being submitted.
- **Missing Macros (Auth)**: The track scope includes `auth` macros, but they are not implemented in the expander. While `auth.*` *operations* exist in the transform layer, they are not exposed as first-class L1 macros, making them inaccessible from L2 pipelines.
- **Documentation (Law System)**: The mechanism for attaching laws and the process for creating a new law checker are completely undocumented. It's unclear how a contributor would add verification for a new algebraic property.
- **Inconsistent Naming (await)**: The `process.await.any` and `process.await.all` macros accept `sources`, `targets`, or `inputs` as the key for the array of events to wait for. This inconsistency is confusing and should be standardized to a single key (e.g., `sources`).
- No macro reference doc for `policy.enforce`, `process.saga`, or `state.diff`; teams must read source to understand inputs/outputs.
- Law suite lacks coverage for policy dominance, saga monotonicity, or `process.await` exclusivity.
- CRDT/jsonpatch notes live in code comments; docs do not surface example payloads or invariants.

## Top issues (synthesized)
- **Release Blocker (Disconnected Law Checking)**: The law verification system is fundamentally flawed. The `state.merge` macro attaches law IDs to L0 nodes, but the corresponding law checker (`laws/crdt-merge.mjs`) **does not read or use them**. Instead, it runs a few hardcoded, static examples. This creates a dangerous illusion of verification; the system is not actually checking the algebraic properties of the code being submitted.
- **Missing Macros (Auth)**: The track scope includes `auth` macros, but they are not implemented in the expander. While `auth.*` *operations* exist in the transform layer, they are not exposed as first-class L1 macros, making them inaccessible from L2 pipelines.
- **Documentation (Law System)**: The mechanism for attaching laws and the process for creating a new law checker are completely undocumented. It's unclear how a contributor would add verification for a new algebraic property.

## Next 3 improvements
- **Fix the law checking system to be dynamic** — Action: Modify the `tf-checker` to iterate through the nodes of the input L0 file. When it finds a node with attached `laws`, it must dynamically load and execute the corresponding law checker against that specific node's properties. The static sample check in `crdt-merge.mjs` should be replaced with this dynamic logic; Impact: Critical. Fixes a major correctness and security gap, ensuring that declared algebraic properties are actually verified; Effort: Large
- **Implement the missing `auth** — Action: Create `auth.mint_token` and `auth.check_token` macros in `packages/expander/expand.mjs` that wrap the existing `Transform` operations; Impact: High. Fulfills a key requirement of the v0.6 feature set and makes authentication capabilities available to L2 pipeline authors; Effort: Medium
- **Document the macro and law extension process** — Action: Create a `docs/0.6/extending-macros.md` guide that explains how to add a new macro to the expander, how to attach laws, and how to create a corresponding law checker module; Impact: High. Empowers contributors to extend the language with new, verified abstractions; Effort: Medium

## References
- [packages/expander/expand.mjs](../../../../packages/expander/expand.mjs)
- [packages/ops/auth.mjs](../../../../packages/ops/auth.mjs)
- [packages/transform/index.mjs](../../../../packages/transform/index.mjs)
- [packages/checker/check.mjs](../../../../packages/checker/check.mjs)
- [laws/crdt-merge.mjs](../../../../laws/crdt-merge.mjs)
- [packages/expander/catalog/state.merge.json](../../../../packages/expander/catalog/state.merge.json)
- [docs/0.6/index.md](../../../../docs/0.6/index.md)
- [packages/expander/tests/state.macros.test.mjs](../../../../packages/expander/tests/state.macros.test.mjs)
- [scripts/pipeline-expand.mjs](../../../../scripts/pipeline-expand.mjs)
- [tools/tf-lang-cli/index.mjs](../../../../tools/tf-lang-cli/index.mjs)
