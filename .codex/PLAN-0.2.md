# v0.2 – Canonicalization, Conformance & Proofs (plan)

This is the authoritative task list for v0.2. Codex must:
- keep TS/Rust semantics mirrored,
- preserve 0.1 behavior,
- update the journal after **every** task.

## Global Guards
- Determinism: canonical JSON + BLAKE3; **no floats in L0** (reject with `E_L0_FLOAT`).
- Lenses: JSON Pointer; overwrite semantics; no implicit creation; fail fast (`E_PTR_*`).
- Delta NF: `null | { replace: final }`.
- Effects NF: `{ read: string[], write: string[], external: string[] }` (sorted unique).
- CALL gate: `sig_hash` must match.
- Tests: TS & Rust unit tests must stay green.

## Directory Map
- TS kernel: `packages/tf-lang-l0-ts/`
- RS kernel: `packages/tf-lang-l0-rs/`
- Shared vectors: `tests/vectors/`
- Explorer: `docs/claims-explorer.html`
- Claims API: `services/claims-api-ts/`
- (Optional) Host-lite: `services/host-lite-ts/`

---

## EPIC A — Canonicalization & Conformance (kernel parity)

### A1. TS canonical JSON + BLAKE3
**Goal:** deterministic bytes + hash; reject floats.  
**Files:**
- `packages/tf-lang-l0-ts/src/canon/json.ts` (export `canonicalJsonBytes`)
- `packages/tf-lang-l0-ts/src/canon/hash.ts` (export `blake3hex`)
**Done when:**
- Unit tests pass locally.
- `canonicalJsonBytes` sorts object keys, preserves arrays, throws `E_L0_FLOAT` for non-integer numbers.
**Verify:**
```bash
pnpm -C packages/tf-lang-l0-ts add @noble/hashes
pnpm -C packages/tf-lang-l0-ts test
A2. Rust canonical JSON + BLAKE3
Files:

packages/tf-lang-l0-rs/src/canon/json.rs (export canonical_json_bytes)

packages/tf-lang-l0-rs/src/canon/hash.rs (export blake3_hex)
Done when: cargo test green; floats rejected.
Verify: cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml

A3. Conformance vectors (shared fixtures)
Files: tests/vectors/{lens_update.json,snapshot_determinism.json,journal_record.json,match_assert.json}
Done when: JSONs load; fields: name, bytecode, inputs, expected.{delta,effect}.

A4. TS conformance runner
Files: packages/tf-lang-l0-ts/scripts/run-vectors.ts + package script "vectors"
Done when: pnpm -C packages/tf-lang-l0-ts vectors prints ✓ for all; nonzero on mismatch.

A5. Rust conformance test
Files: packages/tf-lang-l0-rs/tests/vectors.rs
Done when: cargo test runs vectors and passes.

A6. CI: conformance workflow
Files: .github/workflows/conformance.yml
Done when: PRs & main run TS + RS vectors.

EPIC B — Proof Tags (observability)
B1. Tag interfaces (no behavior change)
Files:

TS: packages/tf-lang-l0-ts/src/proof/tags.ts

RS: packages/tf-lang-l0-rs/src/proof.rs
Tags: Witness, Refutation, Transport, Normalization, Conservativity.
Done when: compiles; no runtime change yet.

B2. Minimal emissions in VM (dev mode)
Change: Emit tags only if DEV_PROOFS=1.

Witness + Normalization on delta/effect

Transport on lens ops

Refutation on assert/sig-hash fail

Conservativity on CALL gate failure
Done when: tests green; tags appear in a dev sink.

EPIC C — Host-lite + Worlds
C1. Minimal HTTP host (in-memory)
Files: services/host-lite-ts/
Endpoints: POST /worlds, GET /worlds, POST /plan, POST /apply, POST /rewind, GET /journal/:id
Done when: curl round-trip works; journal includes proofs if DEV_PROOFS=1.

EPIC D — Legal adapter 0.2
D1. SQLite-backed counts & clauses
Change: services/claims-api-ts to read acts.sqlite + clauses.sqlite.
Endpoints: /facts/count, /clauses return dataset_version and query_hash (canonical bytes + BLAKE3).
Done when: returns real numbers for demo subset; 10+ evidence samples.

EPIC E — Explorer upgrades
E1. Source switcher + sane defaults
Change: docs/claims-explorer.html—keep static file mode; add API URL mode; default to data/claims-ro-mini.json + 2025-09-09.
Done when: both modes render counts.

E2. Render proof tags when present
Done when: “Why” panel shows compact tag list; hidden if none.

EPIC F — CI & Ops
F1. Pages preview on PR (artifact only), deploy on main
Change: pages workflow; badge in README.
Done when: PRs show artifact; main publishes.

F2. GHCR publish (optional)
Change: docker publish workflow for claims-api-ts (and host-lite if present).
Done when: tags 0.2 and latest pushed.

Optimal Order
A1,A2 → A3 → A4 → A5 → A6 → B1 → B2 → C1 → D1 → E1 → E2 → F1 → F2