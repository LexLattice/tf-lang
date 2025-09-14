# Release v0.2 — Notes

This release focuses on determinism, proof-tag tooling, a minimal host API,
SQLite hardening, and improved docs delivery. Changes are grouped by theme and
link back to the originating PRs. Each PR also has an extracted brief under
`briefs/`.

## What Changed

### Kernel determinism and vectors
- Canonical JSON + BLAKE3 hashing in Rust for byte-stable snapshot hashes
  (#7) — key files: `packages/tf-lang-l0-rs/src/canon/*`, `tests/*`.
- Shared conformance vectors and runners for TS and Rust (#8, #11) — key files:
  `tests/vectors/*`, `packages/tf-lang-l0-ts/scripts/run-vectors.ts`,
  `packages/tf-lang-l0-rs/tests/*`, `.github/workflows/conformance.yml`.

### Guardrail ops and proof tags
- Guardrail ops added across TS and Rust (dimension_eq, lens_mod, bounds,
  delta_bounded, saturate) with vectors (#16) — key files: `packages/*/src/ops/*`,
  `tests/vectors/*`.
- Proof tag interfaces for TS/Rust and tests (#20) — key files:
  `packages/tf-lang-l0-ts/src/proof/*`, `packages/tf-lang-l0-rs/src/proof.rs`.
- DEV_PROOFS gating cached and parity-tested; zero overhead when off (#33) — key
  files: `packages/*/src/proof/*`, `packages/*/tests/proof-*`.
- Stable proof tag rendering and hidden panel when none present (#77) — key
  files: `docs/claims-explorer.html`, `packages/explorer-test/*`.

### Host and adapters
- Host‑lite finalized: canonical 400/404, unified exec path, per‑world LRU cache,
  proofs behind `DEV_PROOFS=1` (#46) — key files: `packages/host-lite/src/*`,
  `packages/host-lite/test/*`.
- SQLite adapter hardened: guarded init, prepared statement reuse, SQL‑only
  evidence with byte‑identical JSON across paths (#62) — key files:
  `packages/d1-sqlite/*`, `services/claims-api-ts/src/*`.

### Explorer and Docs delivery
- Source switcher hardening using `/health` meta; defaults and tests package
  extracted (#70) — key files: `docs/claims-explorer.html`,
  `packages/explorer-test/*`.
- GitHub Pages: preview artifact on PRs; deploy from `main` with badge in
  README (#81) — key files: `.github/workflows/pages.yml`, `README.md`.
- CI images: lowercased GHCR repo, reproducibility knob, digest summary (#87) —
  key files: `.github/workflows/ci.yml`, `services/claims-api-ts/Dockerfile`.
- Alignment briefs documentation added (#10) — key files: `.codex/briefs/*`.

## User‑visible changes
- Claims Explorer sorts proof tags and hides the panel when no tags exist (#77).
- Pages workflow publishes `docs/` to a PR artifact and deploys on `main` with a
  live badge in `README` (#81). See Operations doc for access paths.
- Host‑lite exposes POST `/plan` and `/apply` with canonical JSON and 400/404
  behaviors; proofs emit only with `DEV_PROOFS=1` (#46).

## Breaking changes
- None noted. Host and kernel behaviors remain compatible; new features are
  gated or additive.

## PR Index
- #7 — fix: canonical JSON + BLAKE3 for Rust kernel (A2) (see
  `briefs/PR-0007.md`)
- #8 — test: add shared conformance vectors (see `briefs/PR-0008.md`)
- #10 — docs: add alignment briefs A4‑F2 (see `briefs/PR-0010.md`)
- #11 — test: add conformance vector runners in TS and Rust (A4/A5) (see
  `briefs/PR-0011.md`)
- #16 — feat: add guardrail ops and vectors (A7) (see `briefs/PR-0016.md`)
- #20 — feat: add proof tag interfaces (B1) (see `briefs/PR-0020.md`)
- #33 — feat: cache dev proof tags (see `briefs/PR-0033.md`)
- #46 — C1 synthesis: host‑lite finalize (pass‑4) (see `briefs/PR-0046.md`)
- #62 — D1: guard SQLite init and prove prepared reuse (see
  `briefs/PR-0062.md`)
- #70 — E1 pass‑2: explorer source switcher hardening (see
  `briefs/PR-0070.md`)
- #77 — feat: stable proof tag rendering (see `briefs/PR-0077.md`)
- #81 — F1: add pages preview workflow and deployment badge (see
  `briefs/PR-0081.md`)
- #87 — F2 pass‑2: lowercase GHCR, digest summary, reproducibility knob (see
  `briefs/PR-0087.md`)

See individual briefs under `briefs/` for verbatim PR summaries.

