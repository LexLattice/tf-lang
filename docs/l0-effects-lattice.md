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
- `Observability` commutes with `Pure`, other `Observability` nodes, and
  `Network.Out`.
- `Network.Out` commutes with `Pure` and `Observability` nodes.
- `Storage.Write` never commutes with another `Storage.Write` without a
  disjointness proof.
- All other pairs are considered non-commuting for now.

The helper is intentionally directional: `canCommute(prev, next)` answers the
question “may the second node swap with the previous one?” rather than treating
the pair symmetrically. This mirrors how the checker annotates sequential
children—it records whether a future pass could safely bubble the current node
left across its predecessor. Canonicalization combines the directional answers
with a symmetric guard so that we only reorder pairs that commute both ways.

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

## Using the lattice in normalization

The `tf-l0-ir` normalizer applies a local commutation pass after idempotent and
inverse rewrites. Adjacent `Prim` nodes that commute in both directions are
sorted according to `EFFECT_PRECEDENCE`, with the primitive identifier breaking
ties. Effects that cannot commute—such as `Storage.Write`—block reordering,
and region boundaries remain intact, so the pass is purely local and safe.
