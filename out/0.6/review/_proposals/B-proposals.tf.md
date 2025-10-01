# Track B · proposals

### Discoverability (Expander): The macro expansion logic is a core part of the engine, but there is no direct, documented CLI command to perform L2 to L0 expansion. Developers must find wrapper scripts (`pipeline-expand.mjs`) or infer its usage from tests
**Context:** Addresses discoverability (expander): the macro expansion logic is a core part of the engine, but there is no direct, documented cli command to perform l2 to l0 expansion. developers must find wrapper scripts (`pipeline-expand.mjs`) or infer its usage from tests noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "b-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs <some_command_that_expands> examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
node scripts/pipeline-expand.mjs examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml out/auto.fnol.fasttrack.v1.l0.json
node scripts/assert-kernel-only.mjs out/auto.fnol.fasttrack.v1.l0.json
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Code Clarity (Expander): The `preprocessL2Yaml` function in `expand.mjs` uses a fragile, stateful loop with regex to wrap multi-line macros in quotes. This is a common source of parsing errors and is hard to debug. A more robust YAML parsing strategy is needed
**Context:** Addresses code clarity (expander): the `preprocessl2yaml` function in `expand.mjs` uses a fragile, stateful loop with regex to wrap multi-line macros in quotes. this is a common source of parsing errors and is hard to debug. a more robust yaml parsing strategy is needed noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "b-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs <some_command_that_expands> examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
node scripts/pipeline-expand.mjs examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml out/auto.fnol.fasttrack.v1.l0.json
node scripts/assert-kernel-only.mjs out/auto.fnol.fasttrack.v1.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Extensibility (Transform Runner): The `runTransform` function is a single, large `switch` statement. Adding new operations requires modifying this central file, which can lead to merge conflicts and makes the code harder to maintain. A more modular, pluggable architecture would be better
**Context:** Addresses extensibility (transform runner): the `runtransform` function is a single, large `switch` statement. adding new operations requires modifying this central file, which can lead to merge conflicts and makes the code harder to maintain. a more modular, pluggable architecture would be better noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "b-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs <some_command_that_expands> examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
node scripts/pipeline-expand.mjs examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml out/auto.fnol.fasttrack.v1.l0.json
node scripts/assert-kernel-only.mjs out/auto.fnol.fasttrack.v1.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
