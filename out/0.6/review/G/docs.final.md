# Track G · Instance hints & planning

## What exists now
- **Instance Planning CLI**: The `plan-instances` command is implemented in the main CLI (`tools/tf-lang-cli/index.mjs`). It takes an L0 file as input and produces a JSON summary of which instances would be used to execute the nodes.
- **Instance Registry v2**: A rule-based instance registry is located at `instances/registry.v2.json`. The resolution logic (`packages/expander/resolve.mjs`) matches nodes to instances (e.g., `@HTTP`, `@Memory`) based on their `domain` and `channel`.
- **Grouping**: The command's output groups the plan by `domains` (e.g., `interaction`, `obs`) and by `channels` (e.g., `rpc:req`, `metric`). The `--group-by` flag can be used, but its options are not discoverable from help text.
- **Registry v2** (`instances/registry.v2.json`): rule-based selection by domain/QoS/channel with defaults per domain and global fallback.
- **Resolver** (`packages/expander/resolve.mjs`): loads registry.v2 (fallback to registry.json), normalizes channels/QoS, annotates nodes with `runtime.domain` + `runtime.instance`.
- **Planner CLI** (`tf plan-instances`): summarizes counts per domain and per channel scheme, supports `--registry` override and `--group-by domain|scheme`.
- **Tests**: cover fallback when registry.v2 missing, QoS arrays, and explicit overrides.

## How to run (10-minute quickstart)
1. **Generate an instance plan using the default registry**.
```bash
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json
```
2. **Generate a plan using a custom registry file**.
```bash
node tools/tf-lang-cli/index.mjs plan-instances --registry <PATH_TO_REGISTRY>.json <L0_FILE>
```
3. Run command.
```bash
node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
```bash
node tools/tf-lang-cli/index.mjs plan-instances --group-by scheme examples/v0.6/build/auto.quote.bind.issue.v2.l0.json
```
```bash
node tools/tf-lang-cli/index.mjs plan-instances --registry my/registry.json <L0>
```

## Common errors & fixes
| Symptom | Probable cause | Fix |
| --- | --- | --- |
| Running the command without a file path. | The L0 file argument is mandatory. | Provide the path to a valid L0 JSON file. |
| Logical Error (Not a Crash)** | The rules in the instance registry are not specific enough, causing the node to fall through to a default or broader rule. | Add a more specific rule to the `rules` array in the registry JSON file that matches the node's `domain` and `channel`. |
| Missing registry file → planner falls back to `@Memory` silently. Pass `--registry` explicitly in docs/tests to avoid confusion. | Investigate root cause | Document mitigation |
| `--group-by` typo yields `unknown option`; CLI emits usage text but exit code 2 — highlight valid values in docs. | Investigate root cause | Document mitigation |
| Dynamic channels (e.g., `@reply_to_*`) collapse under `dynamic`; provide context when presenting totals so infra teams know these require runtime wiring. | Investigate root cause | Document mitigation |

## Acceptance gates & signals
| Gate | Command | Success signal |
| --- | --- | --- |
| **Generate an instance plan using the default registry** | `node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json` | Command succeeds without errors. |
| **Generate a plan using a custom registry file** | `node tools/tf-lang-cli/index.mjs plan-instances --registry <PATH_TO_REGISTRY>.json <L0_FILE>` | Command succeeds without errors. |
| Run command | `node tools/tf-lang-cli/index.mjs plan-instances examples/v0.6/build/auto.quote.bind.issue.v2.l0.json` | Command succeeds without errors. |
| Run command | `node tools/tf-lang-cli/index.mjs plan-instances --group-by scheme examples/v0.6/build/auto.quote.bind.issue.v2.l0.json` | Command succeeds without errors. |
| Run command | `node tools/tf-lang-cli/index.mjs plan-instances --registry my/registry.json <L0>` | Command succeeds without errors. |

## DX gaps
- **DX (Output Format)**: The output of `plan-instances` is a dense JSON object. While suitable for machine consumption, it is difficult for a human operator to quickly assess the deployment plan. There is no human-readable summary format (e.g., a table).
- **Documentation (Registry v2)**: The rule-based structure of the v2 instance registry, including how rules are matched and the significance of the `default` key, is entirely undocumented. A developer must read the source code of the resolver (`packages/expander/resolve.mjs`) to understand it.
- **Missing "Instance Hints"**: The track is named "Instance Hints & Planning," but there appears to be no mechanism to embed instance hints directly within the L2 or L0 source files. The planning is driven exclusively by the external registry file, which limits per-pipeline customization.
- **No "Dry Run" Visualization**: The plan is abstract. The `tf graph` command shows the logical DAG, but there is no way to visualize the *physical* instance plan (e.g., color-coding nodes by their assigned instance). This makes it hard to understand the operational topology at a glance.
- No documentation for registry schema (fields, wildcards, precedence) beyond code comments.
- Planner output is JSON only; no table/markdown summarizer for release notes.
- Annotated instances are not persisted back into L0 or diagrams, so reviewers cannot see placement decisions without rerunning CLI.

## Top issues (synthesized)
- **DX (Output Format)**: The output of `plan-instances` is a dense JSON object. While suitable for machine consumption, it is difficult for a human operator to quickly assess the deployment plan. There is no human-readable summary format (e.g., a table).
- **Documentation (Registry v2)**: The rule-based structure of the v2 instance registry, including how rules are matched and the significance of the `default` key, is entirely undocumented. A developer must read the source code of the resolver (`packages/expander/resolve.mjs`) to understand it.
- **Missing "Instance Hints"**: The track is named "Instance Hints & Planning," but there appears to be no mechanism to embed instance hints directly within the L2 or L0 source files. The planning is driven exclusively by the external registry file, which limits per-pipeline customization.

## Next 3 improvements
- **Add a human-readable table output to `plan-instances`** — Action: Introduce a `--format table` flag (or make it the default) that prints a clean, aligned summary of the domains, channels, and their assigned instances; Impact: High. Makes the tool immediately useful for human operators trying to understand a deployment plan; Effort: Medium
- **Document the v2 registry and instance hinting** — Action: Create a `docs/0.6/instance-planning.md` guide. It should document the schema for `registry.v2.json`, explain the rule resolution logic, and clarify if/how instance hints can be embedded in source files; Impact: High. Makes a core deployment configuration feature understandable and usable; Effort: Medium
- **Enhance `tf graph` to visualize the instance plan** — Action: Add a `--show-instances` flag to the `tf graph` command. When used, the generated DOT/SVG diagram should color-code each node based on its resolved instance from the registry; Impact: High. Provides an intuitive, visual way to understand the physical deployment topology of a pipeline; Effort: Medium

## References
- [tools/tf-lang-cli/index.mjs](../../../../tools/tf-lang-cli/index.mjs)
- [instances/registry.v2.json](../../../../instances/registry.v2.json)
- [packages/expander/resolve.mjs](../../../../packages/expander/resolve.mjs)
- [examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json](../../../../examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json)
- [examples/v0.6/build/auto.quote.bind.issue.v2.l0.json](../../../../examples/v0.6/build/auto.quote.bind.issue.v2.l0.json)
