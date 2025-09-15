# TF Spec

Defines a minimal intent format for task execution.

## Fields

| Field   | Type   | Description |
|---------|--------|-------------|
| `version` | string | Schema version, currently `0.1` |
| `name`   | string | Human readable spec name |
| `steps`  | array  | Non-empty sequence of steps |
| `steps[].op` | string | Operation identifier |
| `steps[].params` | object | Operation parameters (string/number/boolean values) |

Each step's `params` map only permits primitive values. Nested arrays or objects are invalid.

## Examples

- [vm.json](../../examples/specs/vm.json)
- [copy.json](../../examples/specs/copy.json)
- [multi.json](../../examples/specs/multi.json)

## Versioning

Future versions may extend fields while preserving backward compatibility.
