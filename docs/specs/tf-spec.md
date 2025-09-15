# TF Spec

Defines a minimal intent format for task execution.

## Fields

| Field   | Type   | Description |
|---------|--------|-------------|
| `version` | string | Schema version, currently `0.1` |
| `name`   | string | Human readable spec name |
| `steps`  | array  | Sequence of steps to perform |
| `steps[].op` | string | Operation identifier (see below) |
| `steps[].params` | object | Operation parameters (see below) |

### Supported operations

| Operation | Required params | Description |
|-----------|-----------------|-------------|
| `copy` | `src` (string), `dest` (string) | Copy a file from `src` to `dest` |
| `create_vm` | `image` (string), `cpus` (integer ≥1) | Start a VM using `image` with `cpus` vCPUs |
| `create_network` | `cidr` (string) | Create a network with given CIDR block |

## Examples

- [vm.json](../../examples/specs/vm.json)
- [copy.json](../../examples/specs/copy.json)
- [multi.json](../../examples/specs/multi.json)

## Versioning

Future versions may extend fields while preserving backward compatibility.
