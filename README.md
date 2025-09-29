# TF‑Lang (v0.4) — True Functions, Algebra & Deterministic Pipelines

[![Pages](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml/badge.svg?branch=main)](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml)

**Live site:** [https://LexLattice.github.io/tf-lang/](https://LexLattice.github.io/tf-lang/)

**CI:**
[CI: T4 Plan/Scaffold/Compare](.github/workflows/t4-plan-scaffold-compare.yml) •
[CI: T3 Trace & Perf](.github/workflows/t3-trace-and-perf.yml) •
[CI: L0 Runtime Verify](.github/workflows/l0-runtime-verify.yml) •
[CI: L0 Docs (Sync)](.github/workflows/l0-docs.yml) •
[CI: L0 Proofs (Emit)](.github/workflows/l0-proofs.yml) •
[CI: L0 Audit](.github/workflows/l0-audit.yml)

Version: **v0.4**

---

## What’s in 0.4

**L0 end‑to‑end** (spec → checker → DSL/IR → codegen → provenance/verify → proofs → parity):

* **Spec & Catalog (A0/A1/A2/A3/A4/A5)**

  * Unified **catalog ingest** from YAML, canonical JSON with stable IDs & hashes.
  * **Effects** derivation and an **effect lattice** (Seq/Par safety; commutation hints).
  * **Laws registry** (inverse/idempotent/commutative) backing normalizer/proofs.
  * **Base types & unifier** with sample I/O signatures across families.

* **DSL, IR & Checker (B1–B5)**

  * Minimal **IR** (`Prim|Seq|Par|If|Map|Fold|Retry|Timeout`), JSON codecs, **canonicalizer** (stable hashes).
  * **DSL v1.1** with literals, fmt/show, and **error spans**; `tf-compose` glue:
    `parse` → `check` → `canon` → `emit`.
  * **Policy regions** (`Authorize{…}`) + dominance rules; static **policy auth** checker.

* **Backends & Traces (C1–C6)**

  * **TypeScript codegen** + deterministic **in‑memory adapters** (Network, Storage with idempotency keys & CAS, Crypto with HMAC/verify/hash, Observability).
  * **Rust codegen** (crate scaffolding) + optional **TS↔RS parity** on trace sequences (opt‑in locally).
  * **T3 traces** with **provenance** (IR/manifest/catalog hashes) gated by `TF_PROVENANCE=1`.
  * **Trace validator** (`--require-meta`, hash checks) and **trace‑verify** (composition policy + manifests).

* **Proofs (D1–D5)**

  * Emit **SMT‑LIB** obligations (type/effect safety + laws) and **Alloy** models (Authorize dominance).
  * **Proofs on PR** (emit/upload artifacts; no solver in CI).
  * **Coverage tool** for “what we allow vs what we prove” + **stub emitter** for missing laws.

* **Parity & Pilot (E1–E4)**

  * **Pilot (minimal) via L0** → generated TS path → run → deterministic artifacts.
  * **Parity harness**: generated vs hand‑written runner (equal hashes on fixed seeds).
  * **Runtime verify** workflow: build/run with provenance → schema/meta verify → composition verify; artifacts uploaded.

* **Docs & CI (B6, F1, infra)**

  * **Docgen**: `docs/l0-catalog.md`, `docs/l0-dsl.md`, `docs/l0-effects.md`; drift check in CI.
  * **Repo audit** (schemas/links/determinism/exec bits) with non‑blocking report.
  * **Test taxonomy & unified runners** with filters (product/infra/proofs/parity; fast/heavy).

> **Determinism:** All generated JSON/JSONL is written canonically (stable key order + single trailing newline). Hashes are **SHA‑256**; artifacts placed under `out/0.4/**`.

---

## Quickstart

### A) Standard developer setup

```bash
pnpm -v && node -v
pnpm -w -r install
pnpm -w -r build
```

### B) Codex Cloud setup (one‑liner)

```bash
bash -lc "./scripts/codex/setup.sh"
```

---

## L0: from DSL to runnable pipeline

### Parse, check, canonicalize, emit

```bash
# A0/A1: IDs & Catalog (deterministic)
pnpm run a0
pnpm run a1

# Parse/check/canon a flow
pnpm run tf -- parse examples/flows/signing.tf -o out/0.4/ir/signing.ir.json
pnpm run tf -- check examples/flows/signing.tf -o out/0.4/flows/signing.verdict.json
pnpm run tf -- canon examples/flows/signing.tf -o out/0.4/ir/signing.canon.json

# Generate TS skeleton + runtime
pnpm run tf -- emit --lang ts examples/flows/signing.tf --out out/0.4/codegen-ts/signing
```

### Run with deterministic adapters

```bash
# Provide capabilities manifest (effects + write prefixes)
node out/0.4/codegen-ts/signing/run.mjs --caps tests/fixtures/caps-observability.json

# (optional) Add provenance meta to each trace record
TF_PROVENANCE=1 node out/0.4/codegen-ts/signing/run.mjs --caps tests/fixtures/caps-observability.json
```

### Validate & verify traces (schema + meta + composition)

```bash
# Extract expected hashes from status
IR=$(jq -r .provenance.ir_hash out/0.4/pilot-l0/status.json)
MF=$(jq -r .provenance.manifest_hash out/0.4/pilot-l0/status.json)
CG=$(jq -r .provenance.catalog_hash out/0.4/pilot-l0/status.json)

# Validate trace JSONL against schema and meta
node scripts/validate-trace.mjs --require-meta --ir "$IR" --manifest "$MF" --catalog "$CG" \
  < out/0.4/pilot-l0/trace.jsonl

# Verify trace against IR+manifest (and status)
node packages/tf-compose/bin/tf-verify-trace.mjs \
  --ir out/0.4/pilot-l0/pilot_min.ir.json \
  --manifest out/0.4/pilot-l0/pilot_min.manifest.json \
  --status out/0.4/pilot-l0/status.json \
  --trace out/0.4/pilot-l0/trace.jsonl
```

---

## Pilot (minimal) — build, run, parity

```bash
# Generated TS path (pilot_min) with fixed clock for determinism
TF_FIXED_TS=1750000000000 node scripts/pilot-build-run.mjs

# Hand‑written minimal runner (same adapters), for parity
TF_FIXED_TS=1750000000000 node scripts/pilot-handwritten.mjs

# Parity (generated vs manual)
node scripts/pilot-parity.mjs
cat out/0.4/parity/report.json
```

> **Full pilot parity** (replay→strategy→risk→exec→ledger) is available behind `TF_PILOT_FULL=1` on small slices and may be heavier; see `docs/pilot-l0.md`.

---

## Proofs & Coverage

```bash
# Emit SMT laws/properties and Alloy models (artifacts only; no solver in CI)
node scripts/emit-smt-laws-suite.mjs -o out/0.4/proofs/laws
node scripts/emit-alloy-auth.mjs examples/flows/auth_missing.tf -o out/0.4/proofs/auth/missing.als

# Coverage: what we allow (lattice) vs what we prove (laws)
pnpm run proofs:coverage
pnpm run proofs:emit-missing   # writes skeleton .smt2 for missing commutations
```

Artifacts are uploaded by **L0 Proofs (Emit)** on PRs; see the CI job for downloads.

---

## Docs & Reference

* **Catalog:** `docs/l0-catalog.md`
* **DSL Cheatsheet:** `docs/l0-dsl.md`
* **Effects/Lattice:** `docs/l0-effects.md`
* **Proofs Guide:** `docs/l0-proofs.md`
* **Pilot & Parity:** `docs/pilot-l0.md`
* **Rust Codegen (notes):** `docs/l0-rust.md`

Regenerate docs locally:

```bash
pnpm run docs:gen
# CI will fail the Docs job if these files drift
```

---

## Test Suite (taxonomy & filters)

Every test declares metadata at the top:

```js
// @tf-test kind=product area=checker speed=fast deps=node
```

Rust tests use sidecars: `*.meta` with `kind/area/speed/deps`.

**Commands**

```bash
# List available tests (writes out/0.4/tests/available.json)
pnpm run tests:list

# Fast default (product + infra)
pnpm run test

# Focused subsets
pnpm run test:product
pnpm run test:infra
pnpm run test:proofs        # emit-only proofs
pnpm run test:parity        # TS↔RS; may skip locally if Rust missing
pnpm run test:fast
pnpm run test:heavy         # opt-in; may require LOCAL_RUST or deps
```

CI uses these filters per job; manifests are uploaded as artifacts.

---

## CI overview (high level)

* **A0/A1 determinism:** build spec, run fast tests, ensure canonical artifacts.
* **Docs Sync:** regen `docs/l0-*.md`, run fast tests, fail on drift.
* **L0 Runtime Verify:** build/run pilot with provenance; validate schema/meta; composition verify; upload report.
* **L0 Proofs (Emit):** write SMT/Alloy artifacts & coverage; upload.
* **L0 Audit:** repo‑wide audit (schemas/links/determinism/exec bits); non‑blocking report.
* **Conformance (opt‑in):** TS↔RS parity (trace sequence); Rust toolchain cached.

---

## Determinism & Provenance

* Canonical JSON/JSONL writer with **stable key order** and **single trailing newline**.
* Status files include **provenance**: `ir_hash`, `manifest_hash`, `catalog_hash`, `caps_effects`, `caps_source`.
* With `TF_PROVENANCE=1`, each trace record carries a `meta{…}` block; the validator and verifier can enforce equality.

---

## Repository Map

```
packages/
  tf-compose/                # CLI: parse/check/canon/emit/manifest/verify/policy-auth
  tf-l0-spec/                # A0/A1: catalog ingest, effects/laws scaffolding
  tf-l0-ir/                  # IR schema, codecs, canonicalizer
  tf-l0-check/               # types/effects/lattice, checker glue
  tf-l0-codegen-ts/          # TS codegen + runtime + in‑memory adapters
  tf-l0-codegen-rs/          # Rust codegen (crate scaffolding)
  tf-l0-proofs/              # SMT & Alloy emitters, coverage tools
  tf-l0-tools/               # trace validator/summary/verify, digest utils
crates/                      # Rust support crates (generator/eval)
examples/flows/              # sample DSL flows (signing, run_publish, pilot_min, auth_*.tf)
docs/                        # generated references (catalog, DSL, effects, proofs, pilot)
schemas/                     # shared JSON Schemas (trace, manifest, catalog, etc.)
scripts/                     # build/run/parity/verify/docgen/proofs/audit/test runners
out/0.4/                     # deterministic artifacts (ignored by git)
```

---

## Jules 0.5 DX bundle

* Review notes live under `out/0.5/review-jules/` (tracks A–F plus summary/issues).
* To share as an archive, generate it locally instead of committing the tarball:

  ```bash
  tar -czf out/0.5/review-jules.tar.gz -C out/0.5 review-jules
  ```

---

## Contributing

* PRs must produce **deterministic artifacts** (same seed ⇒ same hashes).
* Tests: prefer **in‑memory adapters** and **no network**.
* No `shell:true`, no `eval`. CRLF‑safe file readers (`/\r?\n/`).
* Generated files end with **one** newline and are written via the canonical writer.
* New commutation/idempotency rewrites should reference a **law ID** and be reflected in **proof coverage**.

---

## License

MIT

---

**Changelog excerpt**

* v0.4 — L0 algebra + checker + DSL/IR + TS/Rust codegen + provenance + runtime verify + proofs + (minimal) pilot parity; docgen, audit, and standardized tests in CI.
* v0.3 — T3 traces & perf harness; T4 plan/scaffold/compare; T5 pilot (TS path) with deterministic artifacts and hashes.

---

*Tip:* for local CI parity, we provide `act` shims under `scripts/ci/local.sh` and guard GH‑only steps with `if: ${{ !env.ACT }}`.
