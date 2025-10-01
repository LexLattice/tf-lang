# Port type metadata reference

`metadata.port_types` annotates L0 nodes with expected payload descriptors so the typechecker can verify bindings and suggest adapters. Each descriptor mirrors the schema in [`schemas/type/port.schema.json`](../../schemas/type/port.schema.json).

## Descriptor shape

A descriptor is an object with at least a `schemaRef` key. Optional `format`, `version`, and custom keys provide additional specificity.

```json
{
  "schemaRef": "schema://policy/payment-request",
  "format": "json",
  "version": "1.0.0"
}
```

Descriptors can appear in three places:

- `node.out.type` — declares the type of the variable produced by `node.out.var`.
- `metadata.port_types.out[varName]` — overrides or augments output descriptors keyed by variable name.
- `metadata.port_types.in[portPath]` — declares the expected type for an input port (supports nested structures).

## Input lookup rules

When resolving `metadata.port_types.in`, the typechecker walks the port path and applies the following fallbacks:

1. Match the exact key (e.g., `body`, `headers`, `0`).
2. If the path segment is numeric and no explicit key exists, use `"*"`.
3. If `"*"` is present at any level, it applies to all remaining segments.
4. Fall back to `default` if provided.
5. Finally, fall back to `var` when the descriptor should mirror the source variable.

Example metadata for a service call that inspects a JSON payload and optional headers:

```json
{
  "metadata": {
    "port_types": {
      "in": {
        "body": { "schemaRef": "schema://claims/fnol-request", "format": "json" },
        "headers": { "*": { "schemaRef": "schema://http/header", "format": "string" } },
        "default": { "schemaRef": "schema://common/opaque" }
      }
    }
  }
}
```

In this example, `body` has a specific schema, every header value resolves via the wildcard rule, and any other port references inherit the opaque default.

## Output descriptors

For outputs, the checker starts with `metadata.port_types.out` and then merges any descriptors referenced directly on `node.out`. If a descriptor is keyed by `default` or `var`, it applies respectively to unnamed outputs or to the variable referenced by `node.out.var`.

```json
{
  "out": { "var": "policyDecision" },
  "metadata": {
    "port_types": {
      "out": {
        "policyDecision": { "schemaRef": "schema://policy/decision", "format": "json" },
        "default": { "schemaRef": "schema://common/opaque" }
      }
    }
  }
}
```

## CLI integration

Read port metadata and compare producer/consumer descriptors:

```bash
pnpm tf typecheck <L0>
```

When a mismatch occurs, the checker searches the adapter registry for a bridge between the actual and expected descriptors. Suggested adapters appear in the CLI summary and can be scaffolded:

```bash
pnpm tf typecheck <L0> --emit-adapters <dir>
```

Missing descriptors simply skip validation. Add `metadata.port_types` to tighten contracts and unlock adapter hints.

## Authoring tips

- Prefer stable `schemaRef` URIs so adapters can be shared across pipelines.
- Use wildcards for uniform map/list shapes (e.g., headers, attachments) instead of enumerating every key.
- Keep descriptors in sync with macro definitions; update both the pipeline and any reference documentation when shapes change.
- Store frequently reused descriptors in catalog macros to avoid duplication.

By annotating port metadata, you enable consistent type inference, clearer CLI diagnostics, and automated adapter scaffolding across TF-Lang pipelines.
