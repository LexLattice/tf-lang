# Trustfall Specification (tf-spec)

This document describes the `tf-spec` format, a JSON-based format for defining Trustfall specifications.

## Scope

The `tf-spec` format is designed to be a portable, language-agnostic representation of a Trustfall query. It can be used to define, validate, and execute queries across different runtimes (e.g., TypeScript and Rust).

## Schema

The `tf-spec` format is defined by the JSON Schema at `schema/tf-spec.schema.json`. The schema defines the structure of a `tf-spec` document, which consists of a `version`, an `id`, and a `root` operation.

### Fields

| Field     | Type      | Description                               |
|-----------|-----------|-------------------------------------------|
| `version` | `string`  | The version of the `tf-spec` schema.      |
| `id`      | `string`  | A unique identifier for this spec.        |
| `root`    | `object`  | The root operation of the spec.           |

### Operations

An operation is a JSON object with an `op` field that specifies the operation to perform, and an optional `args` field that contains an array of nested operations.

## Examples

For concrete examples of `tf-spec` documents, see the files in the `examples/specs/` directory.

## Versioning

The `tf-spec` schema is versioned. This document describes version `0.1`. Future versions may add new fields or operations, but will maintain backward compatibility with existing fields.
