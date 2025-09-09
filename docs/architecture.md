
# TF-Lang L0 — Architecture Notes

- **VM**: SSA bytecode, total & deterministic. JSON values as register values (replace with strict ADTs later).
- **Host interface**: lenses, snapshot id/make, diff apply/invert, journal record/rewind, pure TF call boundary.
- **Checker**: type/effect checker (stub), to evolve to SSA + exhaustiveness + capability-typing.
- **Laws**: encoded as bytecode + ASSERT; CI runs them in both runtimes.
- **Hashing**: `contentHash(canonicalJson(v))` as a placeholder; swap in a canonical JSON + BLAKE3 for cross-runtime equivalence.

See per-runtime READMEs for details.
