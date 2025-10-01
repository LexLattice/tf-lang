# Track D · Examples & Monitors

## What exists now
- **Example Pipelines (L2)**: Two main L2 pipelines are provided under `examples/v0.6/pipelines/`: `auto.fnol.fasttrack.v1.l2.yaml`: An insurance claims fast-tracking process. `auto.quote.bind.issue.v2.l2.yaml`: An insurance quote-to-issue process.
- **Example Monitor (L2)**: One monitor is provided: `examples/v0.6/monitors/fasttrack-24h.l2.yaml`.
- **Build Artifacts (L0)**: Corresponding L0 JSON builds for the pipelines and monitor are present in `examples/v0.6/build/`.
- **Tests**: Each example has a corresponding test spec under `examples/v0.6/tests/` (e.g., `fnol-fasttrack.spec.mjs`).
- **Automation Script**: A shell script, `tasks/run-examples.sh`, exists to orchestrate the expansion, testing, and diagram generation for all examples.
- **Diagrams**: The script generates `.dot` files in the `diagrams/` directory. It also attempts to create `.svg` files if the `dot` command-line tool is installed.
- **Canonical examples** under `examples/v0.6/`: two pipelines (`auto.fnol.fasttrack.v1`, `auto.quote.bind.issue.v2`), one monitor bundle (`fasttrack-24h`).
- **Prebuilt artifacts** in `examples/v0.6/build/*.l0.json` enable downstream tooling without re-expansion.
- **Spec harness** (`examples/v0.6/tests/*.spec.mjs`): asserts kernel-only nodes, RPC corr/reply pairing, metric tag hygiene, monitor effects (Inbound/Outbound presence).
- **Docs**: `docs/0.6/pipelines/*.md` and `docs/0.6/monitors/fasttrack-24h.md` embed DOT snapshots for visual review.

## How to run (10-minute quickstart)
1. The canonical way to run the examples is via the provided shell script.
```bash
bash tasks/run-examples.sh
```
2. Run command.
```bash
node examples/v0.6/tests/quote-bind-issue.spec.mjs --l0 examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
```bash
node examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs --l0 examples/v0.6/build/monitors.fasttrack-24h.l0.json
```
```bash
bash tasks/run-examples.sh   # currently fails on inline comments
```

## Common errors & fixes
| Symptom | Probable cause | Fix |
| --- | --- | --- |
| `invalid call syntax: transform.validate(schema: "FnolV1", input: "@receive.body") # types: in.input={schemaRef:"FnolV1",format:"json"}; out={schemaRef:"FnolV1",format:"json"}` | The `run-examples.sh` script fails during the expansion of the first pipeline (`auto.fnol.fasttrack.v1.l2.yaml`). The YAML pre-processor in the expander (`packages/expander/expand.mjs`) incorrectly includes the comment (`# types: ...`) as part of the macro string, causing a parsing failure. | Remove the inline comment from the `validate_fnol` step in the L2 YAML file. This allows the script to proceed, but reveals the underlying fragility of the parser. |
| Spec scripts exit with `Missing --l0 <path>` if flag omitted; always pass explicit path even when running from build dir. | Investigate root cause | Document mitigation |
| Regenerating from L2 hits the same inline `# types | ` comment parsing bug; strip trailing comments before running the scripts. | ` comment parsing bug; strip trailing comments before running the scripts. |
| DOT → SVG conversion requires Graphviz (`dot`). Without it, the script silently skips SVG emission; advise `apt-get install graphviz` for doc reviewers. | Investigate root cause | Document mitigation |

## Acceptance gates & signals
| Gate | Command | Success signal |
| --- | --- | --- |
| The canonical way to run the examples is via the provided shell script | `bash tasks/run-examples.sh` | Command succeeds without errors. |
| Run command | `node examples/v0.6/tests/quote-bind-issue.spec.mjs --l0 examples/v0.6/build/auto.quote.bind.issue.v2.l0.json` | Command succeeds without errors. |
| Run command | `node examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs --l0 examples/v0.6/build/monitors.fasttrack-24h.l0.json` | Command succeeds without errors. |
| Run command | `bash tasks/run-examples.sh   # currently fails on inline comments` | Command succeeds without errors. |

## DX gaps
- **Release Blocker (Broken Examples)**: The primary example workflow is broken out of the box. A new contributor running `tasks/run-examples.sh` will immediately hit a fatal error, creating a major onboarding hazard and blocking release.
- **DX (Fragile Parser)**: The root cause of the broken example is the fragile YAML pre-processor that cannot handle inline comments. This was also identified in Track B, but its impact is most visible here.
- **Documentation (Missing Guidance)**: There is no `README.md` in `examples/v0.6/` to explain what the examples are, what they demonstrate, or how to run them. A user has to discover the `run-examples.sh` script in a different directory (`tasks/`).
- **Diagrams (Tool Dependency)**: The script's ability to generate user-friendly SVG diagrams depends on the `dot` utility being installed on the system, but this dependency is not documented. If `dot` is missing, only the less accessible `.dot` files are created.
- No README tying the three example commands together or mapping artifacts → docs.
- `tasks/run-examples.sh` fails immediately, so CI-friendly smoke is unavailable.
- Monitor spec docs lack explanation of effect expectations (why Outbound/Inbounds appear) beyond the DOT.

## Top issues (synthesized)
- **Release Blocker (Broken Examples)**: The primary example workflow is broken out of the box. A new contributor running `tasks/run-examples.sh` will immediately hit a fatal error, creating a major onboarding hazard and blocking release.
- **DX (Fragile Parser)**: The root cause of the broken example is the fragile YAML pre-processor that cannot handle inline comments. This was also identified in Track B, but its impact is most visible here.
- **Documentation (Missing Guidance)**: There is no `README.md` in `examples/v0.6/` to explain what the examples are, what they demonstrate, or how to run them. A user has to discover the `run-examples.sh` script in a different directory (`tasks/`).

## Next 3 improvements
- **Fix the broken example pipeline** — Action: Remove the inline comment in `auto.fnol.fasttrack.v1.l2.yaml`. As a follow-up to the Track B recommendation, replace the fragile parser with a robust solution that ignores comments correctly; Impact: Critical. Unblocks the entire example workflow and allows for successful execution of `run-examples.sh`; Effort: Small (for the immediate fix), Medium (for the parser refactor)
- **Add a `README.md` to the `examples/v0.6/` directory** — Action: Create a `README.md` file that explains the purpose of each example, lists the per-example commands, and points to `tasks/run-examples.sh` as the main E2E script; Impact: High. Provides clear, contextual guidance for new developers wanting to understand the system through its examples; Effort: Small
- **Document and handle the `dot` dependency gracefully** — Action: Add a note to the new `README.md` about the `dot` dependency for SVG generation and include installation instructions (e.g., `sudo apt-get install graphviz`). Modify the `run-examples.sh` script to print a clear warning if `dot` is not found, rather than failing silently; Impact: Medium. Improves the user experience by making diagram generation more reliable and transparent; Effort: Small

## References
- [examples/v0.6/pipelines/](../../../../examples/v0.6/pipelines)
- [examples/v0.6/monitors/fasttrack-24h.l2.yaml](../../../../examples/v0.6/monitors/fasttrack-24h.l2.yaml)
- [examples/v0.6/build/](../../../../examples/v0.6/build)
- [examples/v0.6/tests/](../../../../examples/v0.6/tests)
- [tasks/run-examples.sh](../../../../tasks/run-examples.sh)
- [packages/expander/expand.mjs](../../../../packages/expander/expand.mjs)
- [examples/v0.6/](../../../../examples/v0.6)
- [docs/0.6/pipelines/](../../../../docs/0.6/pipelines)
- [docs/0.6/monitors/fasttrack-24h.md](../../../../docs/0.6/monitors/fasttrack-24h.md)
- [examples/v0.6/tests/quote-bind-issue.spec.mjs](../../../../examples/v0.6/tests/quote-bind-issue.spec.mjs)
- [examples/v0.6/build/auto.quote.bind.issue.v2.l0.json](../../../../examples/v0.6/build/auto.quote.bind.issue.v2.l0.json)
- [examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs](../../../../examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs)
- [examples/v0.6/build/monitors.fasttrack-24h.l0.json](../../../../examples/v0.6/build/monitors.fasttrack-24h.l0.json)
