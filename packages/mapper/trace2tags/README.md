# @tf-lang/trace2tags

Maps execution traces into a deterministic tag stream consumed by the coverage generator.

## Mapping rules

- `copy` → `resource.copy`
- `create_vm` → `resource.vm`
- `create_network` → `resource.network`

Each output tag includes the spec name, version, step index, and canonical metadata (sorted keys, newline-terminated JSON).

Generate canonical artifacts with:

```bash
pnpm --filter @tf-lang/trace2tags run build
pnpm --filter @tf-lang/trace2tags run artifacts
```

This reads `fixtures/traces.jsonl` and writes `out/t2/trace-tags.json`.
