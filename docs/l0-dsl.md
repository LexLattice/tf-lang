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

Arguments accept rich literal values in addition to bare identifiers. You can mix
numbers (including negatives and floats), booleans, `null`, arrays, and nested
objects with either quoted or bare keys:

```
write-object(
  key="alpha",
  count=2,
  flags=[true, false, null],
  meta={retry:{count:2, strategy:"linear"}}
)
```

Arrays may include trailing commas and object keys are normalized to strings.

## Formatting and inspection

Use the compose CLI to keep flows tidy and to inspect the parsed tree:

* `tf fmt flow.tf` prints the canonical layout (pass `-w`/`--write` to update the file).
  Running `fmt` multiple times is idempotent.
* `tf show flow.tf` renders a tree view of the IR with two-space indentation.

## Error reporting

Parse failures include a `line:col` location and a short caret span to highlight
the offending token, e.g.:

```
Expected literal at 3:5
  write-object(value=[1,,2])
    ^^
```

The canonicalizer flattens nested `Seq` blocks before applying registered algebraic laws.
It collapses idempotent primitives, eliminates declared inverse pairs, and swaps commute-with-pure primitives across adjacent pure nodes.
Normalization never moves steps across `Region{}` or `Par{}` boundaries, so localized effects stay fenced.
Running the canonicalizer twice yields the same result, keeping canonical hashes deterministic.
