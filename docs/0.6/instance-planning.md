# Instance Planning Guidance (v0.6)

Instance planning bridges the gap between an L0 pipeline's runtime metadata and the deployment registries that ultimately bind each node to infrastructure. Authors can now inspect plans in both machine-readable and tabular formats, annotate pipelines with optional hints, and explain how a selection was made.

## CLI overview

Use `pnpm tf plan` (alias `plan-instances`) to summarize the instances that will be provisioned for a compiled L0 document:

```bash
pnpm tf plan <L0_FILE>
```

Key flags:

- `--registry <path>` – load an alternate registry instead of the built-in defaults.
- `--group-by domain|scheme` – choose the primary grouping (domains by default).
- `--format json|table` – render JSON (default) or a human-readable table.
- `--explain` – attach per-node explanations showing the rule, domain override, or default that chose an instance along with any author-provided hints.

When `--format table` is used, `tf plan-instances` prints two blocks: a primary grouping (domains or schemes) with totals per instance, followed by the complementary view. Adding `--explain` appends a "Details" section that enumerates each kernel node with its domain, channel scheme, resolved instance, and any hints.

In JSON mode, `--explain` augments the output with a `details` array that carries the same information so downstream tooling can surface discrepancies or confirmations programmatically.

## Hints, registries, and precedence

L2 authors can declare `instance_hints` in their pipeline source to suggest preferred bindings for a macro alias or a fully-qualified node identifier:

```yaml
pipeline: demo.pipeline
steps:
  - receive: interaction.receive(endpoint: 'api/demo')
instance_hints:
  receive: "@EdgeHTTP"
  S_receive: "@BlueCluster"
```

Hints appear in the expanded L0 DAG under `runtime.hint`. They are **non-binding**—the planner still resolves the effective `runtime.instance` using the active registry—yet both values are surfaced so humans can see when registry policy disagrees with author intent. If a hint matches the resolved value, the details view records it as a confirmation; otherwise it highlights the delta and shows the registry selection.

Registry precedence now follows this order:

1. **Pipeline hint** (`runtime.hint`) – informational only; never overrides policy but is reported for reconciliation.
2. **Registry rule** – first matching rule by channel, domain, or QoS.
3. **Domain default** – the registry's domain-level default if no rule matched.
4. **Global default** – the registry's fallback when no other selection applies.

Because hints are surfaced alongside registry results, delivery teams can iteratively align policy with author expectations without mutating the DAG itself.

## Worked example

To inspect the fast-track FNOL pipeline in the repository:

```bash
pnpm tf plan examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --format table --explain
```

The table view shows how interaction, observation, and transformation domains map to instances. The appended details list includes entries like:

```
- S_receive (Subscribe) → @HTTP [domain=interaction, scheme=rpc:req]
  source: registry rule 1 (domain="interaction", channel="rpc:req:*")
  hint: @Memory (differs → resolved @HTTP)
```

This makes it clear that the default L0 artifact carried an old `@Memory` hint while registry policy steers the receive node to the `@HTTP` driver.

For a machine-consumable report that downstream systems can ingest, request JSON with details:

```bash
pnpm tf plan examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --format json --explain
```

The result contains `domains`, `schemes`, and a `details` array describing each node. This output is stable across runs and is suitable for regression tests or dashboards.

## Registry references

The canonical registry lives in `instances/registry.v2.json`. Planning also accepts pipeline-specific registries passed via `--registry`, which makes it easy to simulate alternate deployments. For example, `examples/v0.6/registry/fasttrack.instances.json` demonstrates a fast-track rollout where interaction channels prefer `@HTTPPrimary`. The CLI merges hints from the L0 file with whichever registry you provide—without mutating the DAG—so planners can validate proposed rollouts against policy before any infrastructure binding occurs.

