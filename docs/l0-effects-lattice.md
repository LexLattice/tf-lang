# L0 Effects Lattice

This document captures the conservative partial order and commutation surface that the
L0 checker exposes today. The goal is to make the current assumptions explicit so we
can tighten or relax rules as proofs become available.

## Families

The lattice currently tracks the following effect families:

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

The list mirrors the families already attached to catalog primitives. Additional
families can be introduced later, but changes should flow through this lattice so
ordering behaviour remains auditable.

## Partial order (⊑)

`Pure` is the unique bottom element: `Pure ⊑ X` for any effect family `X`. No other
non-trivial orderings are defined. This keeps the structure intentionally flat so
unproven relationships do not leak into the checker.

The ordering is only used as a helper when reasoning about commutation. It does **not**
change type subtyping or authorisation behaviour.

## Sequential commutation

Two neighbouring effects in a sequential program may commute only when the lattice
says so. The conservative table is:

- `Pure` commutes with every family. This allows pure operations to bubble across
  side effects during normalisation.
- `Observability` commutes with `Pure` and with another `Observability` effect.
  Logging across logging is safe, but logging across writes or network output stays
  ordered until we have laws that guarantee otherwise.
- `Network.Out` commutes with `Pure` and with `Observability`. Emitting telemetry or
  network traffic may be reordered after observability operations, but not across
  storage writes.
- `Storage.Write` never commutes with another `Storage.Write` unless a disjointness
  proof is available. We currently treat them as non-commuting.
- All remaining combinations are left unordered by default.

The checker annotates sequential nodes with a `commutes_with_prev` boolean whenever a
neighbouring swap would be legal. Future sprints can build on that metadata to perform
actual rewrites or feed canonicalisation heuristics.

## Parallel safety

Parallel composition is safe by default unless both sides perform writes. Two storage
writes in parallel are **unsafe** unless we can prove their URIs are disjoint. The
lattice helper defers to the existing footprint `conflict` check and accepts an
optional `disjoint(uriA, uriB)` predicate so future proofs can provide stronger
knowledge.

All non-write combinations are treated as parallel-safe. This keeps the parallel
checker simple while still catching the dangerous cases.

## Tooling

`packages/tf-l0-check/src/effect-lattice.mjs` exposes reusable helpers:

- `effectOf(primId, catalog)` returns the best-known effect family using catalog data
  or conservative heuristics.
- `canCommute(prevFamily, nextFamily)` answers whether a sequential swap is safe.
- `parSafe(famA, famB, ctx)` answers whether parallel execution is safe, using
  optional footprint context for storage writes.

`scripts/lattice-report.mjs` materialises the lattice as JSON under
`out/0.4/check/lattice-report.json`. The report contains both the commutation table and
the parallel-safety matrix and is wired into the acceptance workflow to ensure future
changes stay deterministic.

## Relation to proofs

Today’s rules are deliberately strict. Every additional commutation or parallel
relaxation should be justified by a law (for example, a `disjoint(uri)` proof). As
those proofs land, we can extend the lattice in a single place and keep the rest of
the checker honest.
