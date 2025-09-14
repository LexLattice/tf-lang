# TF-Lang v0.1.0 — First cut
**Date:** 2025-09-09

A minimal, deterministic kernel where programs are also proofs of safety. This first release ships two runtimes (TS/Rust), a claims layer, a legal demo, a zero-backend explorer, and a tiny API — all wired with CI and a Docker one-liner.

## Highlights
- L0 VM (TS/Rust) with `ASSERT` + tests for `rewind ∘ apply = id`
- Claims core (schema + algebra + queries)
- Legal adapter (RO mini) with precedence + sample dataset
- Claims Explorer (static) with **Static/API** toggle and **Copy cURL**
- Claims API (Fastify) with CORS
- Docker Compose stack (API + Docs)
- GitHub Pages for `/docs`

## Install / Run
**Docker (recommended)**
```bash
docker compose up --build
# Explorer: http://localhost:8080/claims-explorer.html
# API:      http://localhost:8787
```

**Local (node + pnpm + rust)**
```bash
pnpm i
pnpm -C packages/claims-core-ts build
pnpm -C packages/adapter-legal-ts build
pnpm -C services/claims-api-ts build
PORT=8787 pnpm -C services/claims-api-ts start
# serve docs
cd docs && python -m http.server 8080
```

## Breaking changes
- None. This is the initial public cut.

## Known gaps / Next
- Canonical JSON + BLAKE3 for byte-stable cross-runtime hashing
- Full SSA type/effect checker (exhaustiveness; capability typing)
- Delta algebra with invertibility/compensation proofs
- Minimal TF registry with manifests & semver
- Richer legal parsing (NER, exceptions), MUS-based conflict explain

## Verify the law
Both runtimes include tests that exercise `rewind ∘ apply = id` end-to-end in bytecode:
```bash
pnpm -C packages/tf-lang-l0-ts test
cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
```

Have fun! Contributions and issues welcome.
