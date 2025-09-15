# Acceptance — T1_1

## Evidence
- `schema/tf-spec.schema.json` (JSON Schema)
- `docs/specs/tf-spec.md` (schema overview; field table)
- `examples/specs/` (≥3 JSON examples; each explains intent)
- TS/Rust adapters:
  - TS: `packages/tf-lang-l0-ts/src/spec/adapter.ts`
  - Rust: `packages/tf-lang-l0-rs/src/spec/adapter.rs`
- Validation proof:
  - CI job output that each example validates against the schema
  - Round-trip tests passing in both runtimes (parse→canon→serialize)

## CI
- Job **`tf-spec`**:
  - Validate `examples/specs/*.json` against `schema/tf-spec.schema.json` (AJV or similar as a **dev** dep).
  - Run TS/Rust adapter round-trip tests.
  - Upload an artifact `tf-spec/validation.txt` listing each example and “OK”.
- (Optional, nice): add a pre-commit hook that runs schema lint; do not gate merges on local hooks.

## Determinism
- Given the same example input, the adapter round-trip must produce **byte-identical canonical JSON** (use canonical JSON encoder in both runtimes).
- CI re-runs determinism tests twice to assert equality (no time/env dependencies).

## Parity
- TS and Rust adapters produce structurally equivalent representations for the same example inputs (exact field names and value shapes).

## Docs
- `docs/specs/tf-spec.md` added/updated with:
  - What the schema covers (scope)
  - Examples section referencing `examples/specs/`
  - Versioning note for future extensions
