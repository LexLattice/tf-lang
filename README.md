
# TF-Lang Monorepo

A minimal, deterministic kernel for **True-Function** programs with two runtimes:

- `packages/tf-lang-l0-ts` — TypeScript VM + checker stubs + tests (Vitest)
- `packages/tf-lang-l0-rs` — Rust VM + checker stubs + tests (cargo)

This repo uses **pnpm workspaces** to manage JS/TS packages. The Rust crate lives alongside and is built by CI.

## Quickstart

```bash
# TypeScript
cd packages/tf-lang-l0-ts
pnpm i
pnpm test

# Rust
cd packages/tf-lang-l0-rs
cargo test
```

## Structure

- `packages/` — language runtimes
- `docs/` — design notes and specs
- `.github/workflows/ci.yml` — CI for TS and Rust

## Design (E–O–L Mini)

**O (Ontology):** World, Snapshot, Plan, Δ, JournalEntry, Claim, Evidence, Region, Effects.  
**E (Epistemology):** Content addressing (hash of canonical JSON), determinism, provenance-totality, property tests.  
**L (Logic):** Laws: (1) `rewind ∘ apply = id` at entry boundaries, (2) snapshot determinism, (3) capability-typed effects.

## Roadmap

- Canonical JSON encoder for byte-stable hashing across runtimes.
- Real type/effect checker (SSA, exhaustiveness).
- Delta algebra + invertibility/compensation laws.
- Minimal TF registry with semver + manifests.


---

## Legal adapter demo (RO mini)

Build & run:
```bash
pnpm i
pnpm -C packages/claims-core-ts build
pnpm -C packages/adapter-legal-ts build
node packages/adapter-legal-ts/dist/examples/ro-mini/build.js
```

Expected output:
- Counts of FORBIDDEN per jurisdiction at a fixed date
- Any unresolved contradictions (where precedence cannot decide)
- Sample evidence entries

---

## GitHub Pages

This repo publishes the `docs/` folder to GitHub Pages on every push to `main` via `.github/workflows/pages.yml`.
- Markdown is rendered as static pages (no Jekyll build needed).
- To preview locally, open `docs/index.md` in your markdown viewer.

Once pushed to GitHub, enable Pages:
1) Settings -> Pages -> Build and deployment -> Source: **GitHub Actions**.
2) Push to `main`. The site will deploy automatically.


---

## Claims API (services/claims-api-ts)

A tiny Fastify service that serves the same query surface as the demo:
- `GET /claims/count?modality=FORBIDDEN&jurisdiction=RO&at=2025-09-09`
- `GET /claims/list?modality=FORBIDDEN&jurisdiction=RO&at=2025-09-09&limit=10&offset=0`
- `GET /claims/explain/:id`

Run locally:
```bash
pnpm i
pnpm -C packages/claims-core-ts build
pnpm -C services/claims-api-ts build
PORT=8787 pnpm -C services/claims-api-ts start
# in another shell
curl 'http://localhost:8787/claims/count?modality=FORBIDDEN&jurisdiction=RO&at=2025-09-09'
```

By default it loads data from `services/claims-api-ts/data/claims.json`. Use `CLAIMS_DATA=/path/to/claims.json` to override.


---

## Docker demo (API + Docs)

Bring up both the **Claims API** (on :8787) and the **Claims Explorer** static site (on :8080):

```bash
docker compose up --build
# open http://localhost:8080/claims-explorer.html
# switch Source -> Live API (http://localhost:8787)
```

Stop:
```bash
docker compose down
```


---

## Release v0.1.0

Tag and push:
```bash
git tag -a v0.1.0 -m "TF-Lang v0.1.0: L0 kernels, Claims core, Legal adapter, Explorer & API"
git push origin v0.1.0
```

GitHub Actions will create a release with auto-notes. You can paste [`RELEASE_NOTES_v0.1.0.md`](./RELEASE_NOTES_v0.1.0.md) into the description if you want a curated overview.
