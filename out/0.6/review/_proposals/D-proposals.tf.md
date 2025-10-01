# Track D · proposals

### Release Blocker (Broken Examples): The primary example workflow is broken out of the box. A new contributor running `tasks/run-examples.sh` will immediately hit a fatal error, creating a major onboarding hazard and blocking release
**Context:** Addresses release blocker (broken examples): the primary example workflow is broken out of the box. a new contributor running `tasks/run-examples.sh` will immediately hit a fatal error, creating a major onboarding hazard and blocking release noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "d-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
bash tasks/run-examples.sh
node examples/v0.6/tests/quote-bind-issue.spec.mjs --l0 examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
node examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs --l0 examples/v0.6/build/monitors.fasttrack-24h.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Ensure release gate flips green once command returns success.

### DX (Fragile Parser): The root cause of the broken example is the fragile YAML pre-processor that cannot handle inline comments. This was also identified in Track B, but its impact is most visible here
**Context:** Addresses dx (fragile parser): the root cause of the broken example is the fragile yaml pre-processor that cannot handle inline comments. this was also identified in track b, but its impact is most visible here noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "d-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
bash tasks/run-examples.sh
node examples/v0.6/tests/quote-bind-issue.spec.mjs --l0 examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
node examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs --l0 examples/v0.6/build/monitors.fasttrack-24h.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Documentation (Missing Guidance): There is no `README.md` in `examples/v0.6/` to explain what the examples are, what they demonstrate, or how to run them. A user has to discover the `run-examples.sh` script in a different directory (`tasks/`)
**Context:** Addresses documentation (missing guidance): there is no `readme.md` in `examples/v0.6/` to explain what the examples are, what they demonstrate, or how to run them. a user has to discover the `run-examples.sh` script in a different directory (`tasks/`) noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "d-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
bash tasks/run-examples.sh
node examples/v0.6/tests/quote-bind-issue.spec.mjs --l0 examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
node examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs --l0 examples/v0.6/build/monitors.fasttrack-24h.l0.json
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
