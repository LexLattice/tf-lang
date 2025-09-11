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
  - corrected vector semantics: version tag L0, RFC 6901 pointers, reg0 final state, array subs, null deltas where appropriate
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

## [A3] Conformance vectors (shared fixtures)
- Start: 2025-09-11 02:40 UTC
- End:   2025-09-11 02:50 UTC
- Lessons consulted:
  - A1 – canonicalization rules
  - A2 – VM hashing parity
- Plan:
  - create shared vector fixtures for lens update, snapshot determinism, journal record, match assert
  - ensure each JSON includes name, bytecode, inputs, expected.{delta,effect}
  - parse JSON to verify validity
- Changes:
  - Files touched:
    - tests/vectors/lens_update.json
    - tests/vectors/snapshot_determinism.json
    - tests/vectors/journal_record.json
    - tests/vectors/match_assert.json
  - Key decisions:
    - drafted minimal bytecode programs covering core operations
- Verification:
  - Commands run:
    - node -e "const fs=require('fs'), path=require('path'), dir='tests/vectors'; fs.readdirSync(dir).filter(f => f.endsWith('.json')).forEach(f => JSON.parse(fs.readFileSync(path.join(dir, f)))); console.log('ok');"
  - Results:
    - JSON parsed without error
- Challenges / Notes:
  - corrected vector semantics: version tag L0, RFC 6901 pointers, reg0 final state, array subs, null deltas where appropriate
- Next suggested step:
  - A4

## [A4] TS conformance runner
- Start: 2025-09-11 02:50 UTC
- End:   2025-09-11 03:15 UTC
- Lessons consulted:
  - A1 – canonical JSON + BLAKE3
  - A2 – snapshot hashing parity across runtimes
  - A3 – vector structure, delta/effect expectations
- Plan:
  - implement runner script that loads vectors and executes VM
  - track and normalize effects (reads/writes/external)
  - compare delta and effect via canonicalJsonBytes; print hex diff on mismatch
  - wire up package script `vectors`
- Changes:
  - Files touched:
    - packages/tf-lang-l0-ts/scripts/run-vectors.ts
    - packages/tf-lang-l0-ts/package.json
    - pnpm-lock.yaml
  - Key decisions:
    - wrap DummyHost to track effects
    - use `tsx` for TypeScript execution
- Verification:
  - Commands run:
    - pnpm -C packages/tf-lang-l0-ts build
    - pnpm -C packages/tf-lang-l0-ts vectors
  - Results:
    - build succeeded
    - vectors runner reported ✓ for all vectors
- Challenges / Notes:
  - none
- Next suggested step:
  - A5

## [A5] Vector report & lint
- Start: 2025-09-11 03:15 UTC
- End:   2025-09-11 03:35 UTC
- Lessons consulted:
  - A1 – canonical JSON + BLAKE3
  - A4 – conformance runner structure
- Plan:
  - lint vectors for version tag, pointer format, and CONST→LENS dst:0 pattern
  - emit machine-readable run summary with hashes for delta and effect
- Changes:
  - Files touched:
    - packages/tf-lang-l0-ts/scripts/run-vectors.ts
  - Key decisions:
    - blake3 hashes computed from canonical JSON bytes
    - write report to tests/vectors/.out/ts-report.json
- Verification:
  - Commands run:
    - pnpm -C packages/tf-lang-l0-ts build
    - pnpm -C packages/tf-lang-l0-ts vectors
  - Results:
    - build succeeded
    - vectors runner produced ts-report.json and ✓ for all vectors
- Challenges / Notes:
  - installed missing tsx dependency before running vectors
- Next suggested step:
  - A6
## [A5-rs] Rust conformance test
- Start: 2025-09-11 04:05 UTC
- End:   2025-09-11 04:45 UTC
- Lessons consulted:
  - A4 – conformance runner structure
  - A5 – vector lint and reporting
- Plan:
  - load shared vector fixtures and execute VM with effect-tracking host
  - normalize delta/effect and compare via canonical bytes
  - emit rs-report.json for cross-runtime hashing
  - run cargo tests
- Changes:
  - Files touched:
    - packages/tf-lang-l0-rs/tests/vectors.rs
  - Key decisions:
    - implemented RFC 6901 pointer get/set with overwrite semantics
    - recorded read/write/external effects via interior-mutability wrapper
- Verification:
  - Commands run:
    - cargo fmt --manifest-path packages/tf-lang-l0-rs/Cargo.toml
    - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml --tests -- --nocapture
    - pnpm -C packages/tf-lang-l0-ts build
    - pnpm -C packages/tf-lang-l0-ts vectors
  - Results:
    - formatting completed
    - all Rust tests passed including vectors (1)
    - TypeScript build succeeded
    - TypeScript vectors runner reported ✓ for all fixtures
- Challenges / Notes:
  - missing tsx binary resolved with pnpm install
- Next suggested step:
  - A6
## [A6] CI conformance workflow
- Start: 2025-09-11 04:45 UTC
- End:   2025-09-11 05:10 UTC
- Lessons consulted:
  - A4 – TS vector runner with effect normalization
  - A5 – Rust vector reporting and hashes
  - A1 – canonical bytes for comparisons
- Plan:
  - create compare-reports script to assert cross-runtime parity
  - add conformance workflow invoking lint, TS vectors, Rust tests, comparison, artifacts
  - verify locally in CI order
- Changes:
  - Files touched:
    - .codex/compare-reports.mjs
    - .github/workflows/conformance.yml
  - Key decisions:
    - compare reports via structural equality and hash checks
    - cache pnpm and cargo dependencies in workflow
- Verification:
  - Commands run:
    - node .codex/lint-vectors.mjs
    - pnpm -C packages/tf-lang-l0-ts build
    - pnpm -C packages/tf-lang-l0-ts vectors
    - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml --tests -- --nocapture
    - node .codex/compare-reports.mjs
  - Results:
    - lint ok
    - TS build succeeded
    - TS vectors ✓ and ts-report.json emitted
    - Rust tests passed and rs-report.json emitted
    - reports matched
- Challenges / Notes:
  - needed pnpm install to restore tsx before running vectors
- Next suggested step:
  - B1
## [A6-fix] CI conformance workflow hardening
- Start: 2025-09-11 13:24 UTC
- End:   2025-09-11 13:24 UTC
- Lessons consulted:
  - A6 – cross-runtime compare and artifact upload
  - Node 20 + pnpm cache via actions/setup-node@v4
  - Official pnpm/action-setup@v4 with run_install to avoid missing pnpm
- Changes:
  - Updated `.github/workflows/conformance.yml` to use `pnpm/action-setup@v4` with `version: 10.15.1` and `run_install: true`
  - Kept `actions/setup-node@v4` with `node-version: '20'` and `cache: 'pnpm'`
  - Ensured helper scripts are invoked with `node` (`node .codex/lint-vectors.mjs`, `node .codex/compare-reports.mjs`)
  - Preserved cargo cache, TS build + vectors, Rust tests, artifact upload, and cross-compare steps
- Verification:
  - Commands run:
    - node .codex/lint-vectors.mjs
    - pnpm -C packages/tf-lang-l0-ts build
    - pnpm -C packages/tf-lang-l0-ts vectors
    - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml --tests -- --nocapture
    - node .codex/compare-reports.mjs
  - Results:
    - vector lint ok
    - TS build succeeded
    - TS vectors ✓ and ts-report.json emitted
    - Rust tests passed and rs-report.json emitted
    - cross-runtime compare ok
- Commit:
  - ci: fix pnpm setup and harden conformance workflow (A6)

## [A4/A5] Review fixes – pointer validation, integer detection, host parity
- Start: 2025-09-11 14:00 UTC
- End:   2025-09-11 14:30 UTC
- Lessons consulted:
  - A1 – float rejection
  - A2 – mirrored TS/Rust semantics
  - A4/A5 – conformance runners and vectors
- Plan:
  - Harden JSON Pointer helpers in TS and Rust runners
  - Fix integer vs float detection in Rust vectors
  - Align dummy host delta and TF behaviors with TS
  - Enforce explicit LENS opcode checks in TS runner
  - Verify cross-runtime reports
- Changes:
  - Files touched:
    - packages/tf-lang-l0-ts/scripts/run-vectors.ts
    - packages/tf-lang-l0-rs/tests/vectors.rs
    - .codex/JOURNAL.md
  - Key decisions:
    - Return null for invalid pointer traversals
    - Validate array indices via Number/parse and pad with objects
    - Apply delta NF and plan/delta TF in Rust dummy host
    - Restrict LENS ops to dst:0 explicitly
- Verification:
  - Commands run:
    - pnpm -C packages/tf-lang-l0-ts build
    - pnpm -C packages/tf-lang-l0-ts vectors
    - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml --tests -- --nocapture
    - node .codex/compare-reports.mjs
  - Results:
    - build succeeded
    - vectors ✓ and ts-report.json emitted
    - Rust tests passed and rs-report.json emitted
    - reports match
- Challenges / Notes:
  - needed pnpm install to restore tsx
- Next suggested step:
  - B1

## [A4/A5] Follow-up review fixes – diff_apply concision, ptrSet padding, explicit LENS checks
- Start: 2025-09-11 15:19 UTC
- End:   2025-09-11 15:21 UTC
- Changes:
  - Rust: simplified diff_apply using .get("replace")
  - TS: optimized array padding loop in ptrSet
  - TS: replaced startsWith('LENS_') with explicit opcode checks
- Verification:
  - Commands run:
    - pnpm -C packages/tf-lang-l0-ts build
    - pnpm -C packages/tf-lang-l0-ts vectors
    - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml --tests -- --nocapture
    - node .codex/compare-reports.mjs
    - git grep -n "startsWith('LENS_')" packages/tf-lang-l0-ts/scripts/run-vectors.ts || true
- Results:
    - build succeeded
    - vectors ✓ and ts-report.json emitted
    - Rust tests passed and rs-report.json emitted
    - reports match
    - no startsWith('LENS_') found
- Next suggested step:
  - A7

## [A7] Guardrail ops
- Start: 2025-09-11 16:00 UTC
- End:   2025-09-11 16:30 UTC
- Lessons consulted:
  - A1–A6 for determinism, runners, and pointer rules
- Changes:
  - Added TS and Rust implementations for five guardrail ops
  - Wired dummy hosts to dispatch new ops
  - Added conformance vectors exercising each op
- Verification:
  - pnpm -C packages/tf-lang-l0-ts test
  - pnpm -C packages/tf-lang-l0-ts vectors
  - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
- Results:
  - tests and vectors passed
- Next suggested step:
  - Ontology review

## [A7] Guardrail ops - consolidation
- Start: 2025-09-11 17:00 UTC
- End:   2025-09-11 17:30 UTC
- Lessons consulted:
  - A1–A7
- Changes:
  - Propagate guardrail errors from DummyHost; TfRegistry returns null for unknown IDs
  - Added overflow-safe delta checks and idiomatic ops in TS and Rust
  - Journal saturation corrections and added negative vectors for bounds and delta
  - Effects lists normalized and deduped; vectors capture journal entries
- Verification:
  - pnpm -C packages/tf-lang-l0-ts vectors
  - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
- Results:
  - vectors and tests passed
- Next suggested step:
  - none

## [A7] Polish — delta abs & journal shape
- Start: 2025-09-11 18:00 UTC
- End:   2025-09-11 18:20 UTC
- Changes:
  - Used Math.abs for delta calculation in TS probe
  - Sanitized saturate journal entries to {field,before,after,reason}
  - Dropped redundant clones in Rust vector tests
- Verification:
  - pnpm -C packages/tf-lang-l0-ts vectors
  - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
- Results:
  - vectors and tests passed
## [B1] Proof tags
- Start: 2025-09-11 22:40 UTC
- End:   2025-09-11 22:55 UTC
- Lessons consulted:
  - A1–A7
- Changes:
  - Added proof tag interfaces in TS and Rust with exports
  - Added unit tests demonstrating tag construction
- Verification:
  - pnpm -C packages/tf-lang-l0-ts build
  - pnpm -C packages/tf-lang-l0-ts test
  - cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml --tests
- Results:
  - build succeeded
  - tests passed
- Next suggested step:
  - B2
