# TF Spec

Defines the minimal intent format used by TF-Lang. The schema lives at [`schema/tf-spec.schema.json`](../../schema/tf-spec.schema.json).

## Scope

A spec describes a single operation identifier and its positional arguments.

## Fields

| Field | Type | Required | Description |
| ----- | ---- | -------- | ----------- |
| `tf` | string | yes | Operation identifier (`tf://` URL with version). |
| `args` | array | yes | Positional arguments for the operation. |
| `note` | string | no | Human-readable explanation of the intent. |

## Examples

All examples validate against the schema.

- [`dimension_eq.json`](../../examples/specs/dimension_eq.json)
- [`lens_mod.json`](../../examples/specs/lens_mod.json)
- [`correct_saturate.json`](../../examples/specs/correct_saturate.json)

## Versioning

This document covers schema version 0.1. Future extensions should bump the version while maintaining backward compatibility.
