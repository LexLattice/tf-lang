
# TF-Lang Monorepo

[![deploy](https://github.com/LexLattice/tf-lang/actions/workflows/pages.yml/badge.svg?branch=main)](https://LexLattice.github.io/tf-lang/)

A minimal, deterministic kernel for **True-Function** programs with two runtimes:

- `packages/tf-lang-l0-ts` — TypeScript VM + checker stubs + tests (Vitest)
- `packages/tf-lang-l0-rs` — Rust VM + checker stubs + tests (cargo)

This repo uses **pnpm workspaces** to manage JS/TS packages. The Rust crate lives alongside and is built by CI.

### v0.2 Highlights
- Host‑lite finalized (POST `/plan`, `/apply`), canonical JSON and 400/404.
- Proof tags: shared interfaces, DEV_PROOFS gating, stable Explorer panel.
- SQLite adapter hardening: prepared reuse, SQL‑only evidence and pagination.
- GitHub Pages: PR preview artifact, deploy on `main` with live badge.
- CI images: lowercase GHCR path, digest summary, reproducible builds.
- Release notes: see [docs/releases/v0.2/README.md](docs/releases/v0.2/README.md).

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

## Host-lite (packages/host-lite)

The `host-lite` package provides a minimal, spec-compliant HTTP server for executing TF-lang programs.

- **Endpoints**: `POST /plan` and `POST /apply`.
- **Proofs**: Set `DEV_PROOFS=1` to enable proof generation and emission.

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
- To preview locally, run `make docs-up` and open http://localhost:8080.

Once pushed to GitHub, enable Pages:
1) Settings -> Pages -> Build and deployment -> Source: **GitHub Actions**.
2) Push to `main`. The site will deploy automatically.


---

## Claims API (services/claims-api-ts)

A tiny Fastify service that serves the same query surface as the demo:
- `GET /` — list available endpoints
- `GET /health` — check service health and dataset version
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

By default it loads a static seed dataset from `packages/d1-sqlite/fixtures/seed.sql`.


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

---

## Claims Explorer (zero-backend)

The Explorer is a static page that loads a small dataset and can also talk to the live API:

- Page: `docs/claims-explorer.html`
- Config panel: `docs/config.html` (persists **Source** and **API base** in `localStorage`)
- Toggle **Source** between:
  - **Static file** → `docs/data/claims-ro-mini.json`
  - **Live API** → defaults to `http://localhost:8787`

---

## Idempotent behavior guard (golden check)

We lock demo behavior with `.golden/ro-mini.out.txt`. Recompute and diff:

```bash
pnpm -C packages/claims-core-ts build
pnpm -C packages/adapter-legal-ts build
node packages/adapter-legal-ts/dist/examples/ro-mini/build.js | diff -u .golden/ro-mini.out.txt -
```

If the diff isn’t empty, the change alters behavior. Don’t update `.golden` unless it’s intentional and justified by tests.

---

## Local dev shortcuts

```bash
make setup      # install deps + enable git hooks
make build      # build TS packages
make test       # TS + Rust tests
make golden     # behavior lock check
make api        # start API on :8787
make docs-up    # serve docs on :8080
make docker-up  # compose stack
```

### Git hooks

- **pre-commit** runs the golden check.
- **pre-push** uses a **fast-path**: only tests packages changed in the push range (TS, Rust, or golden).  
  Enable once per clone:
  ```bash
  pnpm run hooks:enable
  ```
  Bypass locally if needed (CI still enforces):
  ```bash
  GIT_BYPASS_GOLDEN=1 git commit -m "wip"   # skip pre-commit golden
  FAST_PATH_DISABLE=1 git push              # force full tests instead of fast-path
  GIT_BYPASS_TESTS=1 git push               # skip pre-push tests
  ```

---

## CI fast-path

You can keep your main workflow and also run a **path-gated** CI (`.github/workflows/ci_fast.yml`) that only triggers relevant jobs (TS, Rust, or golden) when those areas change. Use **Workflow dispatch** to run everything on demand.
