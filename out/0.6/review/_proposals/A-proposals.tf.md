# Track A · proposals

### DX Friction (CLI): Commands are verbose (`node tools/tf-lang-cli/index.mjs ...`). The `pnpm install` log shows warnings that shorter aliases (e.g., `tf-plan`) failed to be created, indicating a broken or incomplete setup in `package.json`
**Context:** Addresses dx friction (cli): commands are verbose (`node tools/tf-lang-cli/index.mjs ...`). the `pnpm install` log shows warnings that shorter aliases (e.g., `tf-plan`) failed to be created, indicating a broken or incomplete setup in `package.json` noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "a-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs --help
node tools/tf-lang-cli/index.mjs validate l2 examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
node tools/tf-lang-cli/index.mjs validate l0 examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
```
**Impact:** Reduces friction for the core developer workflow.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Documentation (Onboarding): The root `README.md` is for v0.5 and does not reflect the v0.6 tools and examples. This creates immediate confusion for new contributors
**Context:** Addresses documentation (onboarding): the root `readme.md` is for v0.5 and does not reflect the v0.6 tools and examples. this creates immediate confusion for new contributors noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "a-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs --help
node tools/tf-lang-cli/index.mjs validate l2 examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
node tools/tf-lang-cli/index.mjs validate l0 examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.

### Documentation (Gaps): `docs/0.6/index.md` explicitly states that detailed v0.6 specification pages are missing. There is no central `CONTRIBUTING.md` to guide new developers on workflow, setup, and testing
**Context:** Addresses documentation (gaps): `docs/0.6/index.md` explicitly states that detailed v0.6 specification pages are missing. there is no central `contributing.md` to guide new developers on workflow, setup, and testing noted in docs.jules.md §Gaps.
**Proposal:**
```yaml
pipeline: "a-fix"
steps:
  - validate: transform.validate(schema: "schemas/l0-dag.schema.json", input: "@input")
  - request:  interaction.request(endpoint: "@http.mock", method: POST, body: { trace: "@trace" })
  - merge:    state.merge(base_ref: "@input", patch: "@proposal", strategy: "jsonpatch")
```
**Acceptance:**
```bash
node tools/tf-lang-cli/index.mjs --help
node tools/tf-lang-cli/index.mjs validate l2 examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
node tools/tf-lang-cli/index.mjs validate l0 examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
```
**Impact:** Clarifies contributor workflow and removes ambiguity.
**Law intent:** Guarantee repeatable outcomes for the described workflow.
