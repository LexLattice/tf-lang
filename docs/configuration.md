# Configuration

This document lists environment variables and config knobs relevant to running
the TF‑Lang monorepo locally and in CI.

## Runtime
- DEV_PROOFS: Emits development proof tags when set to `1`. Defaults to off.
  - Scope: TS and Rust runtimes; host‑lite server forwards tags when enabled.
  - Example (TS): `DEV_PROOFS=1 pnpm -C packages/tf-lang-l0-ts test`
  - Example (Rust): `DEV_PROOFS=1 cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml`

- PORT: Port for the demo API service.
  - Default: `8787`.
  - Example: `PORT=8081 pnpm -C services/claims-api-ts start`

- HOST: Address the demo API binds to.
  - Default: `0.0.0.0`.
  - Example: `HOST=127.0.0.1 pnpm -C services/claims-api-ts start`

## CI (build reproducibility)
- SOURCE_DATE_EPOCH: Set to `0` in the image build job to stabilize timestamps
  inside container layers.
- REGISTRY, REPO_LC: Used by CI to push images to GHCR with a lower‑cased repo
  path. Pushing occurs only from `main`.

These CI variables are configured in `.github/workflows/ci.yml` and do not
affect local development.
