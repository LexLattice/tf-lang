# Reproducible Seeds (TS & Rust)

**Encoding:** 64-bit hex string, e.g. `"0x6f2a7c9bbabc1234"`. Store original + shrink path in the failure JSON.

**PRNG:** Use a minimal, local implementation of XorShift128+ in both runtimes to avoid dependencies.

**Bridge:**
- TS: `seedFromHex(h)` -> `{hi,lo}` -> XorShift128+ state.
- Rust: parse hex → two `u64` limbs → state.
- Convert the first stream of 64-bit words to: ints, bounded ints, booleans, and small arrays. Never call system RNGs.

**Determinism toggles:**
- Fix `now` in `OracleCtx` to a constant during tests.
- Canonicalize floats: `.toFixed(12)` in TS, `format!("{:.12}", x)` in Rust when serialized.

**Emit:**
- `out/t1/harness-seeds.jsonl`: one JSON object per failure `{oracle, runtime, seed, shrinks, note}`.
