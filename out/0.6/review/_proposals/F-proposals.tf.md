# Track F · proposals

### DX (No Autofix/Codegen for Adapters): The typechecker can *suggest* an adapter is needed but provides no way to automatically apply it. A developer must manually insert a new `Transform` node into the L0 file with the correct `spec.op`. This is tedious, error-prone, and requires manual editing of a generated file, which `AGENTS.md` discourages
**Context:** Addresses dx (no autofix/codegen for adapters): the typechecker can *suggest* an adapter is needed but provides no way to automatically apply it. a developer must manually insert a new `transform` node into the l0 file with the correct `spec.op`. this is tedious, error-prone, and requires manual editing of a generated file, which `agents.md` discourages noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "f-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
node tools/tf-lang-cli/index.mjs typecheck <L0_FILE> --adapters <PATH_TO_REGISTRY>.json
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Documentation (Port Typing Syntax): The syntax for defining port types in the `metadata.port_types` block is complex and undocumented. Features like wildcard (`*`) and default ports are used in the typechecker logic but are not explained anywhere
**Context:** Addresses documentation (port typing syntax): the syntax for defining port types in the `metadata.port_types` block is complex and undocumented. features like wildcard (`*`) and default ports are used in the typechecker logic but are not explained anywhere noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "f-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
node tools/tf-lang-cli/index.mjs typecheck <L0_FILE> --adapters <PATH_TO_REGISTRY>.json
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Incompleteness (Capability Lattice): The capability lattice in `policy/capability.lattice.json` only covers `rpc:*` channels. Other channels used in the examples (e.g., `metric:*`, `policy:enforce`) are not defined, meaning the checker will not derive any required capabilities for them. This creates a security and policy blind spot
**Context:** Addresses incompleteness (capability lattice): the capability lattice in `policy/capability.lattice.json` only covers `rpc:*` channels. other channels used in the examples (e.g., `metric:*`, `policy:enforce`) are not defined, meaning the checker will not derive any required capabilities for them. this creates a security and policy blind spot noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "f-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
node tools/tf-lang-cli/index.mjs typecheck <L0_FILE> --adapters <PATH_TO_REGISTRY>.json
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
