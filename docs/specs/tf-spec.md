# TF Spec

Defines a minimal intent format for task execution.

## Fields

| Field   | Type   | Description |
|---------|--------|-------------|
| `version` | string | Schema version, currently `0.1` |
| `name`   | string | Human readable spec name |
| `steps`  | array  | Sequence of steps to perform |
| `steps[].op` | string | Operation identifier |
| `steps[].params` | object | Operation parameters |

## Examples

- [examples/specs](../../examples/specs/) directory
- [vm.json](../../examples/specs/vm.json)
- [copy.json](../../examples/specs/copy.json)
- [multi.json](../../examples/specs/multi.json)

## Versioning

Future versions may extend fields while preserving backward compatibility.

## Allowed operations

| Operation | Required params |
|-----------|-----------------|
| `copy` | `src`, `dest` (strings) |
| `create_vm` | `image` (string), `cpus` (integer ≥1) |
| `create_network` | `cidr` (string) |
