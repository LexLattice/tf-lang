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
