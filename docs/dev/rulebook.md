# Rulebook authoring cheatsheet

This page captures the supported rulebook schema shapes and the tooling that
helps validate them.

## Phase schemas

Phases may be defined either as an array of objects or as a mapping keyed by the
phase id. Both encodings normalize to the same internal structure.

```yaml
phases:
  - id: cp1
    title: "Baseline"
    rules:
      - lint
  - id: cp2
    inherits: [cp1]
    rules:
      - test
```

```yaml
phases:
  cp1:
    title: "Baseline"
    rules:
      - lint
  cp2:
    inherits: [cp1]
    rules:
      - test
```

Phase definitions accept:

- `inherits` – ordered list of phases to include before the phase’s own rules.
- `rules` – either an array of entries or a mapping of rule id to inline
  overrides (see below).
- Any additional metadata you need (titles, descriptions, etc.).

## Rule listings

The top-level `rules` catalog supports mapping and array forms:

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

Within `phase.rules` you can mix plain string references with inline rule
objects. Inline entries must include `id` and any missing fields are inherited
from the matching entry in `rules`.

```yaml
phases:
  cp2:
    inherits: [cp1]
    rules:
      - lint
      - id: test
        expect:
          code: 0
```

When using the mapping form the inline `id` is implied by the key:

```yaml
phases:
  cp2:
    inherits: [cp1]
    rules:
      lint: {}
      test:
        expect:
          code: 0
```

## Normalization rules

`expand.mjs` normalizes rulebooks into a single canonical plan:

- Phases are stored in a `Map<string, Phase>` preserving author order.
- Phase inheritance is depth-first and detects cycles with helpful errors.
- Rule lists are expanded deterministically with duplicate rule ids dropped on
  the second and subsequent occurrences.
- Inline entries merge with the top-level rule catalog; missing `id` fields or
  unknown rule ids raise errors.

Common validation failures include:

- `unknown phase "cp3"`
- `invalid inherits reference "ghost"`
- `cycle detected via "cp1 -> cp2 -> cp1"`
- `unknown rule "lint"`
- `invalid rule entry at phase "cp2"`

## CLI helpers

The CLI exposes two ways to inspect normalized rulebooks:

- `tf-lang run <NODE> <CP> --explain` prints the normalized phase list and the
  expanded rule order before executing probes.
- `node tools/tf-lang-cli/index.mjs explain <rulebook.yml|NODE> <PHASE>` prints
  the same explanation without running any checks.

### Example

The repository includes `tf/blocks/_docs-sample/rulebook.yml` as a minimal
reference:

```yaml
version: 1
meta: { node: docs-sample }
phases:
  cp1:
    title: "Baseline"
    rules: [setup]
  cp2:
    title: "Tests"
    inherits: [cp1]
    rules:
      lint:
        expect:
          code: 0
      test: {}
rules:
  setup:
    kind: shell
    cmd: echo setup
  lint:
    kind: shell
    cmd: echo lint
  test:
    kind: shell
    cmd: echo test
```

Running the CLI explanation highlights the inheritance, normalization, and final
rule order:

```
$ node tools/tf-lang-cli/index.mjs explain tf/blocks/_docs-sample/rulebook.yml cp2
Phases:
 - cp1 — Baseline
 * cp2 — Tests (inherits: cp1)

Expanded rules:
 1. setup — kind=shell, cmd=echo setup
 2. lint — kind=shell, cmd=echo lint
 3. test — kind=shell, cmd=echo test
```

Use these commands when iterating on a rulebook to ensure the normalized plan
matches your expectations.
