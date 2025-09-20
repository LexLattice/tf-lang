# L0 DSL (minimal)

**Grammar (subset):**
```
flow  := step ('|>' step)*
step  := prim | parblock
prim  := IDENT '(' arglist? ')' | IDENT
parblock := 'par{' step (';' step)* '}'

literal := NUMBER | STRING | IDENT | BOOLEAN | NULL | array | object
array := '[' literal (',' literal)* ','? ']'
object := '{' ( (STRING | IDENT) ':' literal ) (',' (STRING | IDENT) ':' literal )* ','? '}'

arglist := IDENT '=' literal (',' IDENT '=' literal)*

Examples:
  serialize |> hash |> sign-data(key_ref="k1")
  par{ a(); b(x=1); c() }
```

The canonicalizer flattens nested `Seq` blocks before applying registered algebraic laws.
It collapses idempotent primitives, eliminates declared inverse pairs, and swaps commute-with-pure primitives across adjacent pure nodes.
Normalization never moves steps across `Region{}` or `Par{}` boundaries, so localized effects stay fenced.
Running the canonicalizer twice yields the same result, keeping canonical hashes deterministic.

## Literals

Arguments accept numbers (including floats with a leading `-`), booleans, `null`, arrays, and objects in addition to identifiers and quoted strings. Arrays and objects allow trailing commas, and object keys may be bare identifiers:

```
write-object(
  key="alpha",
  limit=-1.5,
  flags=[true, false, null],
  meta={retry:{count:2}, note:"memo"}
)
```

## Tooling

Use `tf fmt <flow.tf>` to reformat a flow with sorted argument keys, normalized commas, and one statement per line inside `seq{}`/`par{}` blocks. Pass `-w`/`--write` to update the file in place. Running the formatter multiple times is idempotent.

`tf show <flow.tf>` prints a readable tree view of the parsed IR without modifying any files.

Parser errors now include the failing `line:col` along with a short caret span pointing at the problematic text.
