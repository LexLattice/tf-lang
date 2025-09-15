# TF Spec

## Scope
Defines a minimal intent format covering goals, invariants, gates, lenses and effects/state.

## Fields
| Field | Type | Description |
| --- | --- | --- |
| `version` | string | Schema version identifier |
| `goals` | array[string] | High level objectives |
| `invariants` | array[object] | Each has `path` and `equals` for state assertions |
| `gates` | array[string] | Preconditions that must pass before execution |
| `lenses` | array[object] | View selectors each containing a `path` |
| `effect` | object | Desired resulting state |

## Examples
- [examples/specs/balance.json](../../examples/specs/balance.json)
- [examples/specs/inventory.json](../../examples/specs/inventory.json)
- [examples/specs/profile.json](../../examples/specs/profile.json)

## Versioning
Future revisions may extend fields; `version` indicates the schema revision.
