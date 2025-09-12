# LESSONS (append-only, compact)

# Format: - [TASK][YYYY-MM-DD] Rule: "<short rule>". Guardrail: <test/id>.
- [A1][2025-09-11] Rule: "Reject non-integer numbers (E_L0_FLOAT)." Guardrail: canon:error_on_float
- [A1][2025-09-11] Rule: "Normalize -0 to 0 in canonicalization." Guardrail: canon:-0_normalized
- [A1][2025-09-11] Rule: "Reject unsupported types (NaN/Infinity/BigInt/etc) (E_L0_TYPE)." Guardrail: canon:unsupported_types
- [A1][2025-09-11] Rule: "Snapshot IDs = blake3(canonicalJsonBytes)." Guardrail: snap:blake3_canon_bytes
- [A2][2025-09-11] Rule: "Sort object keys for canonical bytes (Rust)." Guardrail: canon:sorted_keys_rs
- [A2-fix][2025-09-11] Rule: "Normalize '-0' parsed as float zero (Rust)." Guardrail: canon:-0_rs
- [A3][2025-09-11] Rule: "Vectors: L0 tag, RFC6901, reg0 final, array subs, null deltas." Guardrail: vectors:structure_semantics
- [A4][2025-09-11] Rule: "Track/normalize host effects; compare via canonical bytes." Guardrail: runner:effect_tracking_ts
- [A5][2025-09-11] Rule: "Lint vectors: version, pointer format, CONST→LENS dst:0; hash report." Guardrail: vectors:lint_and_hash
- [A5-rs][2025-09-11] Rule: "RFC6901 pointer get/set overwrite; record effects (Rust)." Guardrail: rs:pointers_effects
- [A6][2025-09-11] Rule: "CI compares TS/Rust reports structurally and by hash." Guardrail: ci:cross_runtime_compare
- [A4/A5][2025-09-11] Rule: "Invalid pointer traversal returns null." Guardrail: ptr:null_on_invalid
- [A4/A5][2025-09-11] Rule: "ptrSet validates indices; pad arrays with objects." Guardrail: ptr:set_pad_arrays
- [A4/A5][2025-09-11] Rule: "Dummy host parity TS↔Rust (delta NF; plan/delta TF)." Guardrail: host:parity
- [A4/A5][2025-09-11] Rule: "LENS ops restricted to dst:0; explicit opcode whitelist." Guardrail: lens:dst_only+opcode_whitelist
- [A7][2025-09-11] Rule: "Guardrail ops must propagate errors; hosts must not swallow them." Guardrail: host:propagate_guardrail_errors
- [B1][2025-09-11] Rule: "Proof tags are inert and excluded from hashes." Guardrail: proof:tag_inert
- [B2][2025-09-11] Rule: "Proof tags emitted only when DEV_PROOFS=1." Guardrail: proof:dev_flag
- [B2-polish][2025-09-11] Rule: "Cache feature flags; tests use scoped env guards." Guardrail: proof:env_cache
- [B2-polish2][2025-09-11] Rule: "Proof logs are thread-local; avoid cross-test interference." Guardrail: proof:thread_local_log
