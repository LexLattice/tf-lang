# Rulebook schema

The TF CLI accepts rulebooks expressed in YAML. Each rulebook contains a set of
rule definitions (`rules`) and one or more execution phases (`phases`). This
schema is intentionally flexible to keep existing rulebooks working while
supporting a more ergonomic syntax for new ones.

## Phases

Phases describe which rules run together. They can be written either as an
array of phase objects or as a mapping from phase id to definition.

```yaml
phases:
  - id: base
    rules:
      - lint
  - id: check
    inherits:
      - base
    rules:
      - test
```

```yaml
phases:
  base:
    rules:
      - lint
  check:
    inherits:
      - base
    rules:
      - test
```

Each phase definition supports:

- `inherits` *(optional array of strings)* – phases whose rules are included
  before the current phase.
- `rules` – may be an array (strings or inline rule objects) or a mapping from
  rule id to inline overrides.
- Additional metadata such as `title` is carried through unchanged.

## Rules

The `rules` section can be written as a mapping or an array of rule objects.
Mappings are idiomatic for most rulebooks:

```yaml
rules:
  lint:
    kind: shell
    cmd: pnpm lint
  test:
    kind: shell
    cmd: pnpm test
```

```yaml
rules:
  - id: lint
    kind: shell
    cmd: pnpm lint
  - id: test
    kind: shell
    cmd: pnpm test
```

Within `phase.rules` you may reference a rule by id or define it inline. Inline
rules must include an `id` and can omit other fields that are already defined in
`rules` for the same id. Missing fields are filled from the rule map.

```yaml
phases:
  check:
    rules:
      - lint
      - id: test
        expect: "ok"
```

You can also use the mapping form when a phase lists inline overrides:

```yaml
phases:
  check:
    rules:
      lint: {}
      test:
        expect: "ok"
```

The examples above reuse the `test` rule definition while overriding `expect`.

## Deterministic expansion

When expanding a phase the CLI performs a depth-first traversal of inherited
phases. Rules are de-duplicated by id, keeping the first occurrence that
resolves. The resulting order is deterministic regardless of whether the phase
schema uses arrays or maps.

## Common errors

The CLI reports helpful errors when rulebooks are malformed:

- `unknown phase "id"` – referenced phase is not defined.
- `invalid inherits reference "id"` – a phase inherits from an unknown id.
- `cycle detected via "a -> b -> a"` – inheritance forms a cycle.
- `unknown rule "id"` – rule id is not defined and no inline object is
  provided.
- `invalid rule entry at phase "phase"` – phase rules contain an invalid entry
  (missing `id` or unsupported type).
- `inherits for phase "phase" must be an array` – inheritance list is not an
  array.
- `rulebook phases must be an array or object` – invalid `phases` value.
- `rule definitions must be an array or object` – invalid top-level `rules`
  shape.
