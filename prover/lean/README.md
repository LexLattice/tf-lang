# TF-Lang · Lean 4 Prover Skeleton

This document sketches how the TF-Lang kernel can map into Lean 4. The goal is to
model the immutable L0 DAG directly in a proof assistant so that law checks and
future proofs share a common foundation.

## Kernel model

We can treat the four kernel primitives as an inductive data type. Each node
contains its identifier, inputs, and outputs. Guards (`when`) and metadata are
modeled explicitly so that branch proofs can reason about exclusivity.

```lean
inductive Node
  | transform (id : String) (spec : TransformSpec) (inputs : Inputs) (output : Var)
  | publish   (id : String) (channel : Channel) (payload : Payload) (guard : Guard)
  | subscribe (id : String) (channel : Channel) (filter : Filter) (output : Var)
  | keypair   (id : String) (algorithm : Algorithm) (output : Var)

def Dag := List Node
```

Supporting structures (`TransformSpec`, `Inputs`, `Guard`, etc.) stay minimal at
first—enough to encode the JSON L0 payload. Later passes can refine them to use
stronger types (e.g., enumerations for QoS, dependent pairs for payload shapes).

Determinism facts ("pure transforms are stable"), effect ordering, and policy
membership all become lemmas about the constructed `Dag` value.

## Sample theorem skeleton — CRDT idempotence

The idempotence proof for CRDT publishes can be phrased as a Lean theorem that
assumes a stable correlation identifier and shows replay safety.

```lean
theorem crdt_idempotent
  (dag : Dag)
  (p : Node)
  (h_publish : p ∈ dag)
  (h_channel : p.channel = Channel.rpc "rpc:req:claims/crdt")
  (h_corr : stable_corr p.payload.corr)
  : idempotent dag p := by
  -- Future work:
  -- 1. Unpack the guard and correlation witnesses from `h_corr`.
  -- 2. Use the SMT-style reasoning library to show that two executions with the
  --    same corr collapse to a single state update.
  admit
```

`admit` marks unfinished proof steps. The initial milestone is a type-correct
statement with clear hypotheses. Later iterations can replace `admit` with real
proof terms or calls into Lean's automation. Along the way, the same theorem can
export assumptions that today’s JavaScript law (`laws/idempotency.mjs`) records
manually.

## Next steps

1. Define parsers that lift JSON L0 pipelines into the Lean `Dag` type.
2. Rephrase existing JavaScript law checks as Lean lemmas over `Dag`.
3. Integrate Lean proof artifacts into the CI pipeline once the skeleton passes
   basic elaboration.
