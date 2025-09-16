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

Examples live in [examples/specs/](../../examples/specs/):

- [vm.json](../../examples/specs/vm.json)
- [copy.json](../../examples/specs/copy.json)
- [multi.json](../../examples/specs/multi.json)

## Versioning

Future versions may extend fields while preserving backward compatibility.

## Supported operations

| Operation | Required params | Effect |
|-----------|-----------------|--------|
| `copy` | `src`, `dest` (strings) | Copy a file from `src` to `dest` |
| `create_vm` | `image` (string), `cpus` (integer ≥1) | Create a virtual machine |
| `create_network` | `cidr` (string) | Create a network with the given CIDR |

Additional parameters are rejected.
