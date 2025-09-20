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

The canonicalizer flattens nested `Seq` blocks before applying registered algebraic laws.
It collapses idempotent primitives, eliminates declared inverse pairs, and swaps commute-with-pure primitives across adjacent pure nodes.
Normalization never moves steps across `Region{}` or `Par{}` boundaries, so localized effects stay fenced.
Running the canonicalizer twice yields the same result, keeping canonical hashes deterministic.
