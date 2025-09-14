# v0.2 — Rationale & Non-negotiables

## Purpose
Cross-runtime determinism + observability:
- Canonical JSON + BLAKE3 everywhere
- Delta NF: null | { replace: final }
- Effects NF: { read[], write[], external[] } (sorted unique)
- JSON Pointer lenses (RFC 6901): overwrite; no implicit creation; fail fast
- CALL sig-hash gate (ABI stability)
- Proof tags (dev mode) for Witness/Refutation/Normalization/Transport/Conservativity
- Conformance vectors (TS↔Rust) must match {delta_hash,effect_hash}

## Laws as acceptance gates
- rewind ∘ apply = id (covered via journaling and deltas)
- determinism across TS/Rust (hash equality for vectors)
- no floats in L0 (E_L0_FLOAT)
- no use of nondeterministic sources in runtime (Date/Map/JSON.stringify/etc.)

## Observability
- Journal entries record canonical hashes, snapshots, and proof tags (dev)
