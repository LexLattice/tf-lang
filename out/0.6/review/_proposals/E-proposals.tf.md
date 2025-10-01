# Track E · proposals

### Release Blocker (Disconnected Law Checking): The law verification system is fundamentally flawed. The `state.merge` macro attaches law IDs to L0 nodes, but the corresponding law checker (`laws/crdt-merge.mjs`) does not read or use them. Instead, it runs a few hardcoded, static examples. This creates a dangerous illusion of verification; the system is not actually checking the algebraic properties of the code being submitted
**Context:** Addresses release blocker (disconnected law checking): the law verification system is fundamentally flawed. the `state.merge` macro attaches law ids to l0 nodes, but the corresponding law checker (`laws/crdt-merge.mjs`) does not read or use them. instead, it runs a few hardcoded, static examples. this creates a dangerous illusion of verification; the system is not actually checking the algebraic properties of the code being submitted noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "e-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
steps:
- merge_state: state.merge(strategy: "crdt.gcounter", base: "@...", patch: "@...")
tf-checker
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Missing Macros (Auth): The track scope includes `auth` macros, but they are not implemented in the expander. While `auth.*` *operations* exist in the transform layer, they are not exposed as first-class L1 macros, making them inaccessible from L2 pipelines
**Context:** Addresses missing macros (auth): the track scope includes `auth` macros, but they are not implemented in the expander. while `auth.*` *operations* exist in the transform layer, they are not exposed as first-class l1 macros, making them inaccessible from l2 pipelines noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "e-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
steps:
- merge_state: state.merge(strategy: "crdt.gcounter", base: "@...", patch: "@...")
tf-checker
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Documentation (Law System): The mechanism for attaching laws and the process for creating a new law checker are completely undocumented. It's unclear how a contributor would add verification for a new algebraic property
**Context:** Addresses documentation (law system): the mechanism for attaching laws and the process for creating a new law checker are completely undocumented. it's unclear how a contributor would add verification for a new algebraic property noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "e-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
steps:
- merge_state: state.merge(strategy: "crdt.gcounter", base: "@...", patch: "@...")
tf-checker
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
