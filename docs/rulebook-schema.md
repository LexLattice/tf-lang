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

Inline overrides inherit every field from the base rule unless explicitly
overridden. Only the changed fields need to be written in the phase definition.

```yaml
rules:
  lint:
    kind: shell
    cmd: echo lint
    expect: pass

phases:
  check:
    rules:
      - id: lint
        expect: ok
```

```yaml
rules:
  lint:
    kind: shell
    cmd: echo lint
    expect: pass

phases:
  check:
    rules:
      lint:
        expect: ok
```

Both snippets expand to a rule with `kind: shell` and `cmd: echo lint` while
overriding only `expect: ok` in the phase.

## Deterministic expansion

When expanding a phase the CLI performs a depth-first traversal of inherited
phases. Rules are de-duplicated by id, keeping the first occurrence that
resolves. The resulting order is deterministic regardless of whether the phase
schema uses arrays or maps.

## Common errors

The CLI reports helpful errors when rulebooks are malformed:

- `unknown phase "id"` – referenced phase is not defined.
- `cycle detected in phase inheritance: "a" -> "b" -> "a"` – inheritance forms
  a cycle.
- `unknown rule "id"` – rule id is not defined and no inline object is
  provided.
- `inline rule entry in phase "phase" missing "id"` – an inline object omits
  its identifier.
- `rule entry in phase "phase" must be a string id or an object with "id"` –
  phase rules contain an unsupported entry type.
- `phase "phase" has non-array inherits` – inheritance list is not an array.
- `phase "phase" has non-array rules` – rule list is not an array or mapping.
- `rulebook phases must be an array or object` – invalid `phases` value.
- `rule definitions must be an array or object` – invalid top-level `rules`
  shape.
