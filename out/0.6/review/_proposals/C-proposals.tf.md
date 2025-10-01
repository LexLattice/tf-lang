# Track C · proposals

### Code Duplication (Runtime): The L0 runtime (`packages/runtime/run.mjs`) re-implements the entire `Transform` logic, creating a near-exact copy of the `runTransform` function in `packages/transform/index.mjs`. This is a critical maintenance and correctness hazard
**Context:** Addresses code duplication (runtime): the l0 runtime (`packages/runtime/run.mjs`) re-implements the entire `transform` logic, creating a near-exact copy of the `runtransform` function in `packages/transform/index.mjs`. this is a critical maintenance and correctness hazard noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "c-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node packages/checker/check.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --out out/0.6/review/C/TFREPORT.json
// import { executeL0 } from 'packages/runtime/run.mjs';
// const l0 = JSON.parse(fs.readFileSync('...'));
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Discoverability (Runtime): There is no CLI command to execute an L0 file directly. This makes it difficult for developers to test or debug the runtime behavior of a compiled pipeline without writing a custom script
**Context:** Addresses discoverability (runtime): there is no cli command to execute an l0 file directly. this makes it difficult for developers to test or debug the runtime behavior of a compiled pipeline without writing a custom script noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "c-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node packages/checker/check.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --out out/0.6/review/C/TFREPORT.json
// import { executeL0 } from 'packages/runtime/run.mjs';
// const l0 = JSON.parse(fs.readFileSync('...'));
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### DX (Checker): The checker's output is a monolithic `TFREPORT.json` file. While comprehensive, it can be hard to quickly parse for the specific cause of a failure. A human-readable summary output to the console would improve the user experience
**Context:** Addresses dx (checker): the checker's output is a monolithic `tfreport.json` file. while comprehensive, it can be hard to quickly parse for the specific cause of a failure. a human-readable summary output to the console would improve the user experience noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "c-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node packages/checker/check.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --out out/0.6/review/C/TFREPORT.json
// import { executeL0 } from 'packages/runtime/run.mjs';
// const l0 = JSON.parse(fs.readFileSync('...'));
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
