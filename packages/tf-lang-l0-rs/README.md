
# TF-Lang L0 (Rust skeleton)

A tiny, deterministic kernel for True-Function programs: VM, type/effect checker stubs, and core models.
This is a **skeleton** to iterate on. It compiles to a library and ships a minimal test harness.

## Layout
- `src/model/` — typed artifacts (bytecode, effects, ids).
- `src/vm/` — bytecode interpreter + Host trait for domain hooks.
- `src/check/` — type/effect checker stubs (ready for expansion).
- `tests/` — placeholder “laws” test; expand into property tests.
- `examples/` — tiny program JSON.

## Quickstart
```bash
cd tf-lang-l0-rs
cargo build
cargo test
```

## Notes
- Hashing uses `blake3` (hex strings).
- VM registers are `serde_json::Value` for flexibility; replace with stricter types as the model firms up.
- The Host trait is the boundary to domain-specific logic (lenses, diffs, journal).

MIT-licensed. Have fun.
