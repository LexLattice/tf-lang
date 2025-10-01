# Track H · proposals

### DX (Opaque Prover): The Z3 prover is a critical component, but it's treated like a black box. There is no documentation on how it's invoked, what SMT-LIB code is generated, or how to debug it. The error `solver-failed` provides no actionable information
**Context:** Addresses dx (opaque prover): the z3 prover is a critical component, but it's treated like a black box. there is no documentation on how it's invoked, what smt-lib code is generated, or how to debug it. the error `solver-failed` provides no actionable information noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "h-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs laws --check <L0_FILE> --goal <GOAL>
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive
node tools/tf-lang-cli/index.mjs laws --check out/0.6/review/H/fail_test/fail.l0.json --goal branch-exclusive
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Incompleteness (Shallow Law Checks): The `monotonic_log` and `confidential_envelope` checks are shallow pattern matches, not deep proofs. They check for the *presence* of a certain publish event but don't verify the *content* or *logic* (e.g., that the log is actually append-only, or that plaintext is never exposed alongside ciphertext). This provides a false sense of security
**Context:** Addresses incompleteness (shallow law checks): the `monotonic_log` and `confidential_envelope` checks are shallow pattern matches, not deep proofs. they check for the *presence* of a certain publish event but don't verify the *content* or *logic* (e.g., that the log is actually append-only, or that plaintext is never exposed alongside ciphertext). this provides a false sense of security noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "h-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs laws --check <L0_FILE> --goal <GOAL>
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive
node tools/tf-lang-cli/index.mjs laws --check out/0.6/review/H/fail_test/fail.l0.json --goal branch-exclusive
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Documentation (Goals): The `tf laws` command requires a `--goal` argument, but there is no way to list the available goals. A user must find them by reading the source code or documentation
**Context:** Addresses documentation (goals): the `tf laws` command requires a `--goal` argument, but there is no way to list the available goals. a user must find them by reading the source code or documentation noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "h-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs laws --check <L0_FILE> --goal <GOAL>
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive
node tools/tf-lang-cli/index.mjs laws --check out/0.6/review/H/fail_test/fail.l0.json --goal branch-exclusive
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
