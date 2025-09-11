# v0.2 Build Journal

This file is updated **by the Implementer after each task**.

## Task Zero – Kickoff
- Start: 2025-09-11 01:04 UTC
- End: 2025-09-11 01:10 UTC
- Plan:
  - Review v0.2 plan and master prompt
  - Verify toolchains are installed
  - Ensure repository is clean
- Environment checks:
  - `node -v` → v20.19.4
  - `pnpm -v` → 10.5.2
  - `rustc --version` → 1.89.0
- `cargo --version` → 1.89.0
- First three tasks: A1, A2, A3

[A1] TS canonical JSON + BLAKE3
Start: 2025-09-11 01:10 UTC

End: 2025-09-11 01:18 UTC

Plan:
- add BLAKE3 dependency
- implement canonical json encoder rejecting floats
- hash with blake3
- update VM and docs
- add tests

Changes:
- added canonical JSON encoder and BLAKE3 hashing; updated VM, docs, and tsconfig

Files touched:
- packages/tf-lang-l0-ts/package.json
- packages/tf-lang-l0-ts/src/canon/json.ts
- packages/tf-lang-l0-ts/src/canon/hash.ts
- packages/tf-lang-l0-ts/src/canon/index.ts
- packages/tf-lang-l0-ts/src/index.ts
- packages/tf-lang-l0-ts/src/vm/interpreter.ts
- packages/tf-lang-l0-ts/tests/canon.test.ts
- packages/tf-lang-l0-ts/tsconfig.json
- docs/architecture.md
- pnpm-lock.yaml

Key decisions:
- throw 'E_L0_FLOAT' for non-integer numbers
- set tsconfig rootDir to '.' so tests compile

Verification:
- pnpm -C packages/tf-lang-l0-ts add @noble/hashes
- pnpm -C packages/tf-lang-l0-ts build
- pnpm -C packages/tf-lang-l0-ts test

Commands run:
- pnpm -C packages/tf-lang-l0-ts add @noble/hashes
- pnpm -C packages/tf-lang-l0-ts build
- pnpm -C packages/tf-lang-l0-ts test

Results:
- dependency installed
- build succeeded
- tests passed (6 total)

Challenges / Notes:
- removed stray compiled test outputs after initial build error

Next suggested step:
- A2
[A1] Edge-case locks
Start: 2025-09-11 01:18 UTC

End: 2025-09-11 01:30 UTC

Plan:
- remove non-deterministic JSON.stringify uses
- expand canonicalJsonBytes tests for edge cases
- use canonical bytes for snapshot ids and equality
- expose canonicalJsonBytes and blake3hex from package root

Changes:
- replaced runtime JSON.stringify with canonicalJsonBytes + blake3hex
- added tests for -0, NaN/Infinity, BigInt/function/symbol rejection, deep key ordering
- compared VM states via canonical bytes and explicit exports

Files touched:
- packages/tf-lang-l0-ts/src/canon/json.ts
- packages/tf-lang-l0-ts/src/host/memory.ts
- packages/tf-lang-l0-ts/src/index.ts
- packages/tf-lang-l0-ts/src/vm/interpreter.ts
- packages/tf-lang-l0-ts/tests/canon.test.ts

Key decisions:
- normalize -0 to 0 instead of rejecting
- throw 'E_L0_TYPE' for unsupported data types
- derive snapshot_id via blake3hex(canonicalJsonBytes)

Verification:
- git grep -n "JSON.stringify" packages/tf-lang-l0-ts/src | grep -v tests || true
- pnpm -C packages/tf-lang-l0-ts build
- pnpm -C packages/tf-lang-l0-ts test

Commands run:
- git grep -n "JSON.stringify" packages/tf-lang-l0-ts/src | grep -v tests || true
- pnpm install
- pnpm -C packages/tf-lang-l0-ts build
- pnpm -C packages/tf-lang-l0-ts test

Results:
- only canonical JSON uses remain
- build succeeded
- tests passed (10 total)

Challenges / Notes:
- reinstalling dependencies was required before build

Next suggested step:
- A2
## [A2] Rust canonical JSON + BLAKE3
- Start: 2025-09-11 01:30 UTC
- End:   2025-09-11 01:55 UTC
- Lessons consulted:
  - A1 – float rejection in canonical encoder
  - A1 – -0→0 normalization
  - A1 – canonical snapshot hashing via BLAKE3
- Plan:
  - implement canonical_json_bytes and blake3_hex modules
  - remove placeholder hash module and update VM
  - add tests for key ordering, float rejection, hashing
  - run cargo test
- Changes:
  - Files touched:
    - packages/tf-lang-l0-rs/src/canon/json.rs
    - packages/tf-lang-l0-rs/src/canon/hash.rs
    - packages/tf-lang-l0-rs/src/canon/mod.rs
    - packages/tf-lang-l0-rs/src/lib.rs
    - packages/tf-lang-l0-rs/src/vm/interpreter.rs
    - packages/tf-lang-l0-rs/tests/canon.rs
    - removed packages/tf-lang-l0-rs/src/hash.rs
  - Key decisions:
    - reject non-integer numbers with "E_L0_FLOAT"
    - sort object keys for deterministic bytes
- Verification:
  - Commands run:
    - cargo fmt --manifest-path packages/tf-lang-l0-rs/Cargo.toml
    - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
  - Results:
    - formatting completed
    - all tests passed (8 total)
- Challenges / Notes:
  - none
- Next suggested step:
  - A3

## [A2-fix] Rust canonical JSON follow-up
- Start: 2025-09-11 02:00 UTC
- End:   2025-09-11 02:20 UTC
- Lessons consulted:
  - A1 – canonical snapshot hashing via BLAKE3
  - A1 – deep key-ordering invariance
- Plan:
  - switch test host snapshot_id and eq/json to canonical bytes
  - cover serde_json::from_str("-0") vs "0" and nested key order
  - adjust encoder to accept float zero
  - run cargo fmt and test
- Changes:
  - updated tests/laws.rs to hash snapshots and compare states via canonical bytes
  - expanded tests/canon.rs with from_str("-0") case and nested array/object example
  - canonical_json_bytes now normalizes float zero values
- Verification:
  - git grep -nE "to_string\\(|serde_json::to_string" packages/tf-lang-l0-rs/src || true
  - cargo fmt --manifest-path packages/tf-lang-l0-rs/Cargo.toml
  - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
- Results:
  - grep shows only allowed to_string uses
  - formatting completed
  - tests passed (9 total)
- Challenges / Notes:
  - serde_json parses "-0" as float; had to special-case in encoder
- Next suggested step:
  - A3
