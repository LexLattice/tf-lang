# L0 DSL (minimal)

**Grammar (subset):**
```
flow  := step ('|>' step)*
step  := prim | parblock
prim  := IDENT '(' arglist? ')' | IDENT
parblock := 'par{' step (';' step)* '}'

arglist := IDENT '=' (NUMBER | STRING | IDENT) (',' IDENT '=' (NUMBER | STRING | IDENT))*

Examples:
  serialize |> hash |> sign-data(key_ref="k1")
  par{ a(); b(x=1); c() }
```

## Literals

Arguments accept rich literal forms in addition to bare identifiers:

* Numbers with optional leading `-`: `-42`, `3.14`
* Booleans: `true`, `false`
* `null`
* Arrays with trailing commas allowed on input: `[1, "two", true, null, -0.5]`
* Objects with string or identifier keys: `{name:"alice", retry:{count:2}}`

Nested combinations are supported, e.g.:

```
write-object(meta={retry:{count:2, windows:[1,2,3]}}, tags=[true,false])
```

## Tooling

The CLI includes helpers for working with DSL flows:

* `tf fmt flow.tf` reprints the flow using a canonical layout. Add `--write`/`-w` to update the file in-place. The formatter is idempotent and sorts argument keys, object members, and normalizes commas/semicolons.
* `tf show flow.tf` prints a tree representation of the parsed IR for quick inspection.

Parse errors report a `line:col` location with a short caret span to highlight the offending range, making it easier to pinpoint syntax issues.

The canonicalizer flattens nested `Seq` blocks before applying registered algebraic laws.
It collapses idempotent primitives, eliminates declared inverse pairs, and swaps commute-with-pure primitives across adjacent pure nodes.
Normalization never moves steps across `Region{}` or `Par{}` boundaries, so localized effects stay fenced.
Running the canonicalizer twice yields the same result, keeping canonical hashes deterministic.
