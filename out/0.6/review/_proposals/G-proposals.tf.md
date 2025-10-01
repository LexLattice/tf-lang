# Track G · proposals

### DX (Output Format): The output of `plan-instances` is a dense JSON object. While suitable for machine consumption, it is difficult for a human operator to quickly assess the deployment plan. There is no human-readable summary format (e.g., a table)
**Context:** Addresses dx (output format): the output of `plan-instances` is a dense json object. while suitable for machine consumption, it is difficult for a human operator to quickly assess the deployment plan. there is no human-readable summary format (e.g., a table) noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "g-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
node tools/tf-lang-cli/index.mjs plan-instances --registry <PATH_TO_REGISTRY>.json <L0_FILE>
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Documentation (Registry v2): The rule-based structure of the v2 instance registry, including how rules are matched and the significance of the `default` key, is entirely undocumented. A developer must read the source code of the resolver (`packages/expander/resolve.mjs`) to understand it
**Context:** Addresses documentation (registry v2): the rule-based structure of the v2 instance registry, including how rules are matched and the significance of the `default` key, is entirely undocumented. a developer must read the source code of the resolver (`packages/expander/resolve.mjs`) to understand it noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "g-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
node tools/tf-lang-cli/index.mjs plan-instances --registry <PATH_TO_REGISTRY>.json <L0_FILE>
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Missing "Instance Hints": The track is named "Instance Hints & Planning," but there appears to be no mechanism to embed instance hints directly within the L2 or L0 source files. The planning is driven exclusively by the external registry file, which limits per-pipeline customization
**Context:** Addresses missing "instance hints": the track is named "instance hints & planning," but there appears to be no mechanism to embed instance hints directly within the l2 or l0 source files. the planning is driven exclusively by the external registry file, which limits per-pipeline customization noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "g-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
node tools/tf-lang-cli/index.mjs plan-instances --registry <PATH_TO_REGISTRY>.json <L0_FILE>
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
