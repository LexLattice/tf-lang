# L0 DSL (minimal)

**Grammar (subset):**
```
flow    := step ('|>' step)*
step    := prim | parblock
prim    := IDENT '(' arglist? ')' | IDENT
parblock := 'par{' step (';' step)* '}'

arglist := IDENT '=' literal (',' IDENT '=' literal)*
literal := NUMBER | STRING | IDENT | 'true' | 'false' | 'null' | array | object
array   := '[' (literal (',' literal)* ','?)? ']'
object  := '{' (objkey ':' literal (',' objkey ':' literal)* ','?)? '}'
objkey  := STRING | IDENT
```

Examples:
```
serialize |> hash |> sign-data(key_ref="k1")
par{ a(); b(x=1); c() }
seq{
  write-object(uri="res://kv/bucket", key="x", meta={retry:{count:2}});
  write-object(uri="res://kv/bucket", key="y", flags=[true, false, null])
}
```

Literals accept numbers (with optional leading `-`), booleans, `null`, arrays (with optional trailing commas), and objects with either quoted or bare identifier keys. Nested structures are valid anywhere a literal can appear, so expressions like `write-object(meta={retry:{count:2}})` parse without additional helpers.

The canonicalizer flattens nested `Seq` blocks before applying registered algebraic laws. It collapses idempotent primitives, eliminates declared inverse pairs, and swaps commute-with-pure primitives across adjacent pure nodes. Normalization never moves steps across `Region{}` or `Par{}` boundaries, so localized effects stay fenced. Running the canonicalizer twice yields the same result, keeping canonical hashes deterministic.

## Tooling

### Formatter

```
node packages/tf-compose/bin/tf.mjs fmt flow.tf [--write|-w]
```

The formatter parses the DSL and reprints it with sorted argument keys, normalized commas/semicolons, and stable literal layouts (object keys sorted, arrays comma-separated). Use `--write`/`-w` to update the file in place. Formatting is idempotent, so running it multiple times yields identical output.

### Tree view

```
node packages/tf-compose/bin/tf.mjs show flow.tf
```

`show` renders the parsed IR as a tree with two-space indentation. Each `Prim` displays its identifier and arguments (with sorted keys), which makes it easy to inspect pipelines and block structure without touching the source file.

## Error reporting

Parse failures include a `line:col` suffix and a short caret span pointing at the offending token, e.g.
```
Expected value at 2:11
  write-object(arr=[1,,2])
           ^^
```
This context helps locate issues such as stray commas, unterminated strings, or unbalanced braces quickly.
