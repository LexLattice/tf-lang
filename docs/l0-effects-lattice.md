# L0 Effects Lattice

This sprint introduces an explicit lattice over the L0 effect families so the
checker and future normalizers can reason about ordering and parallelism in a
consistent way. The lattice is intentionally conservative and mirrors the
families already present in the catalog:

- Pure
- Observability
- Storage.Read
- Storage.Write
- Network.In
- Network.Out
- Crypto
- Policy
- Infra
- Time
- UI

`Pure` is the unique bottom element. Every other family is currently
incomparable in the partial order, so the lattice provides only the minimal
structure required for helper logic.

## Sequential commutation rules

The helper `canCommute(prev, next)` determines whether a node in a sequential
composition can safely move left past the previous node. The rules are:

- `Pure` commutes with everything. It contributes no externally observable
  state, so two pure operations can freely swap and a pure node can cross any
  other family.
- `Observability` commutes with `Pure` and with another `Observability` step.
  Swapping an emit/log pair is safe, but we assume no additional relations.
- `Network.Out` commutes with `Pure` and `Observability`. Reordering those does
  not change remote state and is already accepted by downstream proofs.
- `Storage.Write` never commutes with another `Storage.Write` without a proof
  that the writes are disjoint. We intentionally keep the default answer
  negative and defer to richer laws later.
- Every other combination conservatively returns `false`. Future SMT laws can
  add more edges once they are formally justified.

The checker annotates sequential children with a `commutes_with_prev` boolean.
No canonicalization happens yet, but the metadata makes it easy to implement
normalization or linting in later sprints.

## Parallel safety rules

The helper `parSafe(famA, famB, ctx)` answers whether two effects can execute
in parallel. By default everything other than a `Storage.Write` pair is safe.
When both sides write, the helper reuses the existing footprint conflict check
and allows an optional `ctx.disjoint(uriA, uriB)` predicate. Until we have a
formal proof for disjointness, the absence of information keeps parallel writes
unsafe. Future law-driven relaxations can plug into the same hook.

## Effect lookup helper

The helper `effectOf(primId, catalog)` returns the best known effect family. It
prefers catalog data and falls back to a handful of conservative regex rules
when a primitive is missing. This keeps tests stable while the catalog catches
up.

## Reporting and testing

`scripts/lattice-report.mjs` materializes the lattice into
`out/0.4/check/lattice-report.json` so other tools (and humans) can inspect the
commutation and parallel matrices. Twenty checker tests cover the expected
commutation pairs, parallel safety answers, effect lookup behaviour, and report
stability so regressions are caught quickly.

As the proof effort progresses we can extend the lattice with additional
relations, but for now we keep the default posture maximally conservative and
explicitly document each deviation.
