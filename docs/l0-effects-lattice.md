# L0 Effects Lattice

This checker sprint introduces an explicit description of the conservative effect
lattice that powers future normalization work. The current families are:

- `Pure`
- `Observability`
- `Storage.Read`
- `Storage.Write`
- `Network.In`
- `Network.Out`
- `Crypto`
- `Policy`
- `Infra`
- `Time`
- `UI`

`Pure` is the bottom element for commutation purposes: a pure primitive can move
past any other effect family. No other ordering relations are assumed at this
stage; most families are incomparable until we have proofs that justify
reordering.

## Sequential commutation

The checker exposes `canCommute(famA, famB)` which answers whether two effect
families may be swapped in a sequential composition. The conservative table is:

- `Pure` commutes with every family.
- `Observability` commutes only with `Pure` and with other `Observability`
  operations.
- `Network.Out` commutes with `Pure` and `Observability`.
- All other pairs are treated as non-commuting by default, including
  `Storage.Write` with itself.

These answers are surfaced on `Seq` nodes as `commutes_with_prev` annotations so
that future canonicalization passes can see which neighbors are safely movable
without changing semantics.

## Parallel composition

The checker also offers `parSafe(famA, famB, ctx)` to decide whether two
branches may be executed in parallel. The only unsafe case we model today is two
`Storage.Write` effects that target the same URI. The helper delegates to the
existing footprint conflict check when write information is available and accepts
an optional `disjoint(uriA, uriB)` predicate to recognise proven separation.

Non-write effects are considered safe in parallel by default. The lattice does
not yet model other resource constraints; future iterations may tighten these
rules as more footprints or laws become available.

## Integration and reporting

`effectOf(primId, catalog)` resolves a primitive into an effect family using the
catalog whenever possible, falling back to the legacy name-based heuristics that
seeded the catalog. The checker now tags sequential children with commute hints,
while the new `scripts/lattice-report.mjs` writes a canonical JSON matrix to
`out/0.4/check/lattice-report.json`. The matrix captures both commutation and
parallel-safety answers and is locked down via dedicated unit tests.

This foundation lets later sprints relax constraints gradually, guarded by proofs
and laws, without regressing today’s conservative behaviour.
