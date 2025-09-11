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
