# TF Spec

Defines a minimal intent schema with a fixed version and `echo` steps.

## Fields

| Field | Type | Description |
| --- | --- | --- |
| `version` | integer | Schema version (must be `1`). |
| `description` | string | Human description of the intent. |
| `steps` | array | Ordered actions to perform. |
| `steps[].type` | string | Action type; only `echo` is supported. |
| `steps[].message` | string | Message for `echo` steps. |

## Examples

- [hello.json](../../examples/specs/hello.json) — prints hello
- [multi.json](../../examples/specs/multi.json) — prints two messages
- [empty.json](../../examples/specs/empty.json) — no steps

## Versioning

This is version `1` of the schema. Future extensions may add new step types or fields while preserving backward compatibility.
