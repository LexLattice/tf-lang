
# TF-Lang L0 — Architecture Notes

- VM: SSA bytecode, total & deterministic. JSON values as register values
  (replace with strict ADTs later).
- Host interface: lenses, snapshot id/make, diff apply/invert, journal
  record/rewind, pure TF call boundary.
- Checker: type/effect checker (stub), to evolve to SSA + exhaustiveness +
  capability-typing.
- Laws: encoded as bytecode + ASSERT; CI runs them in both runtimes.
- Hashing: `blake3hex(canonicalJsonBytes(v))` for cross‑runtime equivalence.

## Runtime and host updates (v0.2)
- Host‑lite server exposes POST `/plan` and `/apply` only, returns canonical JSON
  and canonical 400/404 errors. Per‑world LRU cache (cap 32). Proof tags are
  emitted only when `DEV_PROOFS=1`.
- Proof tags: shared type interfaces (TS/Rust), deterministic emission when
  enabled, and stable UI ordering in the Explorer.
- D1 SQLite adapter: guarded initialization, prepared statement reuse, and
  SQL‑only pagination/evidence paths. Prepared vs ad‑hoc produce byte‑identical
  JSON.
- Explorer: reads `/health` for dataset version/tags/default date with static
  fallback.

See per‑runtime READMEs for details.
