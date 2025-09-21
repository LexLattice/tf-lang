# L0 Effects Lattice

The L0 checker uses a conservative lattice to describe the relationship between
primitive effect families. The lattice is intentionally small: it only captures
ordering information that we can justify today and treats everything else as
incomparable until we prove otherwise.

## Effect families

Current families:

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

Catalog entries may still use legacy variants such as `Time.Read` or
`Time.Wait`; the lattice normalizes these aliases to the canonical families
above.

## Partial order and commutation

The partial order (⊑) is used strictly as a bookkeeping tool for future
normalization passes. Today the order only tracks a single relationship:
`Pure ⊑ X` for every family `X`. No other pairs are related, which keeps all
non-pure effects incomparable.

The commutation table determines whether a node can be reordered with its
predecessor inside a sequential composition. The rules are asymmetric because
commutation is evaluated relative to a previous effect family:

- `Pure` commutes with everything.
- `Observability` only commutes with `Pure` and other `Observability` nodes.
- `Network.Out` commutes with `Pure` and `Observability` nodes. The reverse is
  *not* assumed; an observability action followed by a network write stays in
  place until we have a proof obligation describing that swap.
- `Storage.Write` never commutes with another `Storage.Write` without a
  disjointness proof.
- All other pairs are considered non-commuting for now.

The checker simply annotates `Seq` children with a `commutes_with_prev` boolean
so that future normalization passes can inspect the lattice decision without
reordering anything yet.

## Parallel safety

The lattice also feeds parallel safety checks. Two `Storage.Write` branches are
unsafe by default unless we can prove they write to disjoint URIs. The helper
exposed to the checker delegates to the existing footprint conflict detector,
so the behavior matches the previous implementation while giving us a single
entry point to relax the rule when disjointness laws become available.

All other effect combinations are treated as parallel-safe, which keeps the
current behavior for non-write pairs intact. The exported helpers support an
optional `disjoint(uriA, uriB)` predicate for future precision without changing
callers.

## Reporting and future work

The lattice report script emits the commutation and parallel-safety matrices
under `out/0.4/check/lattice-report.json`. The JSON output is deterministic so
CI snapshots can track intentional changes when we revise the rules.

Upcoming sprints will reuse these helpers inside the canonicalizer. By carrying
`commutes_with_prev` annotations, we can gate normalization rewrites on the
proven lattice rules and extend the table only when corresponding laws are
formalized.
