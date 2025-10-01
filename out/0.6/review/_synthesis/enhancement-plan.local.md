> **Live Tracking Copy**

## Progress

- **Group 1 — Law & Prover Integrity**
  ☑ Planned ☑ In progress ☑ PR open ☑ Merged ☑ Docs updated
  Owner: Track E/H · Target: 2024-06-07

- **Group 2 — Macro & Example Pipeline Reliability**  
  ☐ Planned ☐ In progress ☐ PR open ☐ Merged ☐ Docs updated  
  Owner: ___ · Target: ___

- **Group 3 — Runtime & Capability Platform**  
  ☐ Planned ☐ In progress ☐ PR open ☐ Merged ☐ Docs updated  
  Owner: ___ · Target: ___

- **Group 4 — Instance Planning Experience**  
  ☐ Planned ☐ In progress ☐ PR open ☐ Merged ☐ Docs updated  
  Owner: ___ · Target: ___

- **Group 5 — Developer Workflow & CLI Cohesion**  
  ☐ Planned ☐ In progress ☐ PR open ☐ Merged ☐ Docs updated  
  Owner: ___ · Target: ___

- **Group 6 — Core Docs & Onboarding**  
  ☐ Planned ☐ In progress ☐ PR open ☐ Merged ☐ Docs updated  
  Owner: ___ · Target: ___

# TF-Lang v0.6 · Enhancement Plan

This plan consolidates the per-track proposals in [`out/0.6/review/_proposals`](../_proposals/INDEX.md) into six execution groups. Each group bundles fixes that share code paths or review owners so we can deliver the v0.6 uplift with minimal context switching. Groups are ordered by dependency and risk: release blockers first, onboarding polish last.

## Group 1 — Law & Prover Integrity
**Proposals covered:** [Track E · Release Blocker (Disconnected Law Checking)](../_proposals/E-proposals.tf.md#release-blocker-disconnected-law-checking), [Track E · Documentation (Law System)](../_proposals/E-proposals.tf.md#documentation-law-system), [Track H · DX (Opaque Prover)](../_proposals/H-proposals.tf.md#dx-opaque-prover), [Track H · Incompleteness (Shallow Law Checks)](../_proposals/H-proposals.tf.md#incompleteness-shallow-law-checks), [Track H · Documentation (Goals)](../_proposals/H-proposals.tf.md#documentation-goals)

**Why this bundle works:** These items all touch the proof surface (laws, Z3 prover, checker UX). Fixing them together lets us redesign the verification pipeline once, plumb the same metadata through, and document the workflow without duplicating effort.

**Implementation steps:**
1. Refactor `laws/crdt-merge.mjs` (and sibling checkers) so they ingest the law IDs emitted by `state.merge`, evaluate real pipeline traces, and emit structured pass/fail evidence.
2. Extend the prover harness to log the generated SMT-LIB, expose invocation flags, and surface actionable diagnostics on `solver-failed`.
3. Deepen the `monotonic_log` and `confidential_envelope` goals by asserting semantic invariants (e.g., append-only ordering, absence of plaintext alongside ciphertext).
4. Introduce `tf laws --list-goals` (or equivalent) and document the law authoring workflow plus checker integration steps in a dedicated guide.

**Joint acceptance:**
```bash
node tools/tf-lang-cli/index.mjs laws --list-goals
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --goal branch-exclusive --verbose
node tools/tf-lang-cli/index.mjs laws --check out/0.6/review/H/fail_test/fail.l0.json --goal confidential-envelope --expect-fail
node tools/tf-lang-cli/index.mjs check-l2 --laws-report out/0.6/review/E/law-audit.json examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml
```

**Impact:** Restores trust in automated proofs, unblocks release gating, and equips contributors with transparent law tooling.

## Group 2 — Macro & Example Pipeline Reliability
**Proposals covered:** [Track B · Code Clarity (Expander)](../_proposals/B-proposals.tf.md#code-clarity-expander), [Track D · Release Blocker (Broken Examples)](../_proposals/D-proposals.tf.md#release-blocker-broken-examples), [Track D · DX (Fragile Parser)](../_proposals/D-proposals.tf.md#dx-fragile-parser), [Track E · Missing Macros (Auth)](../_proposals/E-proposals.tf.md#missing-macros-auth)

**Why this bundle works:** All four issues revolve around L2→L0 expansion and the YAML pre-processor. Solving them together lets us replace the fragile parsing layer, add missing macro coverage, and re-run the example suite once.

**Implementation steps:**
1. Replace `preprocessL2Yaml` with a streaming YAML loader (e.g., `yaml` AST) that natively handles inline comments and multi-line macros.
2. Add automated regression fixtures for the previously failing inline-comment cases and pipe them through `tasks/run-examples.sh`.
3. Implement the `auth.*` macro family in the expander so auth pipelines compile without hand-editing L0.
4. Rerun and harden `tasks/run-examples.sh` (plus scenario-specific tests) to certify the examples are green under the new parser.

**Joint acceptance:**
```bash
pnpm test --filter "examples:v0.6"
node tools/tf-lang-cli/index.mjs expand examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml --out out/0.6/tmp/auto.fnol.fasttrack.v1.l0.json
bash tasks/run-examples.sh
node examples/v0.6/tests/quote-bind-issue.spec.mjs --l0 examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```

**Impact:** Unlocks clean macro expansion, keeps flagship examples runnable, and introduces auth macros without extra maintenance cost.

## Group 3 — Runtime & Capability Platform
**Proposals covered:** [Track B · Extensibility (Transform Runner)](../_proposals/B-proposals.tf.md#extensibility-transform-runner), [Track C · Code Duplication (Runtime)](../_proposals/C-proposals.tf.md#code-duplication-runtime), [Track C · Discoverability (Runtime)](../_proposals/C-proposals.tf.md#discoverability-runtime), [Track F · DX (No Autofix/Codegen for Adapters)](../_proposals/F-proposals.tf.md#dx-no-autofixcodegen-for-adapters), [Track F · Incompleteness (Capability Lattice)](../_proposals/F-proposals.tf.md#incompleteness-capability-lattice)

**Why this bundle works:** Each proposal touches the execution core and capability inference. By modularizing the transform runner once, we can reuse adapters, share capability metadata, and expose a supported runtime CLI.

**Implementation steps:**
1. Break `runTransform` into pluggable handlers (per op) and share that registry with the runtime executor to eliminate duplication.
2. Introduce a public `tf runtime exec <file.l0.json>` command that shells into the unified execution engine with tracing hooks.
3. Generate adapter stubs directly from `tf typecheck` suggestions, wiring them into the handler registry.
4. Expand `policy/capability.lattice.json` (and tests) to cover non-`rpc:*` channels, ensuring the checker enforces new adapters and auth flows.

**Joint acceptance:**
```bash
node tools/tf-lang-cli/index.mjs runtime exec examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --trace
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --emit-adapters out/0.6/tmp/adapters/
node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.quote.bind.issue.v2.l0.json --capabilities-report out/0.6/tmp/capabilities.json
node packages/checker/check.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --out out/0.6/tmp/TFREPORT.json
```

**Impact:** Simplifies execution pathways, keeps capability enforcement honest, and turns adapter suggestions into one-click fixes.

## Group 4 — Instance Planning Experience
**Proposals covered:** [Track G · DX (Output Format)](../_proposals/G-proposals.tf.md#dx-output-format), [Track G · Documentation (Registry v2)](../_proposals/G-proposals.tf.md#documentation-registry-v2), [Track G · Missing "Instance Hints"](../_proposals/G-proposals.tf.md#missing-instance-hints)

**Why this bundle works:** Instance planning spans tooling and docs. Tackling output formatting, registry explanation, and hint embedding together lets us redesign the UX holistically.

**Implementation steps:**
1. Layer a human-readable summary (table + diff) atop the existing JSON output of `tf plan-instances`.
2. Document registry rule precedence, defaults, and hint resolution in `examples/v0.6/` and link to it from the CLI help.
3. Add an `instance_hints` block to L2 schemas, propagate it through expansion, and merge with registry decisions at plan time.

**Joint acceptance:**
```bash
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --format table
node tools/tf-lang-cli/index.mjs plan-instances --registry examples/v0.6/registry/fasttrack.instances.json examples/v0.6/build/auto.quote.bind.issue.v2.l0.json --format table
node tools/tf-lang-cli/index.mjs plan-instances --explain
```

**Impact:** Gives operators immediate situational awareness and documents how to steer deployments without spelunking through source code.

## Group 5 — Developer Workflow & CLI Cohesion
**Proposals covered:** [Track A · DX Friction (CLI)](../_proposals/A-proposals.tf.md#dx-friction-cli), [Track B · Discoverability (Expander)](../_proposals/B-proposals.tf.md#discoverability-expander), [Track C · DX (Checker)](../_proposals/C-proposals.tf.md#dx-checker)

**Why this bundle works:** These items all focus on everyday CLI entry points. Addressing aliases, discoverable commands, and richer checker output together creates a cohesive command suite.

**Implementation steps:**
1. Wire `package.json` bin aliases (e.g., `tf plan`, `tf expand`) and ensure `pnpm install` exposes them without warnings.
2. Promote macro expansion to a first-class CLI (`tf expand`) with documented flags and parity against internal scripts.
3. Augment `tf check` to emit a human-readable summary alongside `TFREPORT.json`, including capability gaps and law statuses.

**Joint acceptance:**
```bash
pnpm tf --help
pnpm tf expand examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml --out out/0.6/tmp/auto.fnol.fasttrack.v1.l0.json
pnpm tf check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --summary
pnpm tf check examples/v0.6/build/auto.quote.bind.issue.v2.l0.json --summary
```

**Impact:** Delivers intuitive commands, shortens feedback loops, and surfaces checker insights without JSON spelunking.

## Group 6 — Core Docs & Onboarding
**Proposals covered:** [Track A · Documentation (Onboarding)](../_proposals/A-proposals.tf.md#documentation-onboarding), [Track A · Documentation (Gaps)](../_proposals/A-proposals.tf.md#documentation-gaps), [Track D · Documentation (Missing Guidance)](../_proposals/D-proposals.tf.md#documentation-missing-guidance), [Track F · Documentation (Port Typing Syntax)](../_proposals/F-proposals.tf.md#documentation-port-typing-syntax)

**Why this bundle works:** These changes are editorial and benefit from a shared editorial calendar. Once upstream tooling is stable (Groups 1–5), the docs team can reflect the final UX with one cohesive update.

**Implementation steps:**
1. Refresh the root `README.md` and add a v0.6 onboarding quickstart that references the stabilized CLI commands.
2. Create a contributor guide covering setup, example workflows, and where to find macro/law references.
3. Add `examples/v0.6/README.md` with scenario descriptions, run commands, and troubleshooting tips.
4. Publish a focused reference on `metadata.port_types`, including wildcard/default semantics and validator behavior.

**Joint acceptance:**
```bash
rg "v0.5" README.md docs/ out/0.6/review -n
pnpm tf expand --help | sed -n '1,40p'
pnpm tf check --help | sed -n '1,40p'
node tools/link-checker.mjs out/0.6/review
```

**Impact:** Aligns public documentation with the new workflows, smoothing onboarding for v0.6 contributors.

---

**Next steps:** Execute groups sequentially, feeding learnings from early deliveries (laws, parser, runtime) into the documentation pass. Track progress in `out/0.6/review/_summary/ALL.md` to keep ownership and target dates visible.
