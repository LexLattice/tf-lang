# C1 — Changes (Run 3)

## Summary
Refined `host-lite` to harden error handling and determinism. Added explicit malformed JSON 400s, method gating, and multi-world LRU proofs while keeping proofs gated.

## Why
- Advances END_GOAL by ensuring canonical idempotent `/plan` and `/apply` responses with bounded per-world cache and proof toggling.

## Tests
- Added: malformed JSON 400, method 404, multi-world cache bounds.
- Updated: boundary scan for package imports.
- Determinism/parity: repeated `pnpm test` runs stable; no sockets/files/network.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
