# Trace schema → Tag mapping

The execution adapters emit traces with the following structure:

```json
{
  "spec": { "name": "demo-plan", "version": "0.1" },
  "events": [
    {
      "stepIndex": 0,
      "op": "copy",
      "outcome": "success",
      "params": { "src": "bucket-a", "dest": "bucket-b" },
      "details": { "src": "bucket-a", "dest": "bucket-b" }
    }
  ]
}
```

Fields:

- `spec` — identifying metadata for the plan under test.
- `events` — ordered list of execution steps.
  - `stepIndex` — original index from the spec.
  - `op` — operation name (subset: `copy`, `create_vm`, `create_network`).
  - `outcome` — currently only `success`; reserved for future error states.
  - `params` — canonicalised step parameters.
  - `details` — adapter-enriched metadata (resource identifiers, computed values).

The mapper converts each successful event into a deterministic tag:

| Operation | Tag | Metadata |
| --- | --- | --- |
| `copy` | `resource.copy` | `{ "src": string, "dest": string }` |
| `create_vm` | `resource.vm` | `{ "id": string, "image": string, "cpus": number }` |
| `create_network` | `resource.network` | `{ "id": string, "cidr": string }` |

Tags are written to `out/t2/trace-tags.json` as a canonical JSON array (sorted keys, newline terminated). The coverage generator consumes this file to compute aggregate coverage.
