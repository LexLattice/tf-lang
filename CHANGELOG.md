# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2025-09-09
### Added
- **L0 runtimes:** TypeScript and Rust VMs with SSA bytecode, `ASSERT` opcode, and property-like tests for the law `rewind ∘ apply = id`.
- **Hashing:** Content hashing helpers (placeholder canonical JSON) for snapshot/bytecode IDs.
- **Checker stubs:** Type/effect checker skeletons ready for SSA + exhaustiveness.
- **Claims core:** Domain-agnostic Claim schema, scope overlap & opposition, contradiction detection, and query helpers (count/list/at).
- **Legal adapter (RO mini):** Regex-based deontic extractor, simple legal precedence (National > Local; newer > older; more specific > generic), and a small demo corpus.
- **Docs site:** GitHub Pages publishing of `/docs` with overview and quickstarts.
- **Claims Explorer (zero-backend):** Static HTML page for Counts → Drilldown → Why; loads JSON.
- **Explorer ↔ API toggle:** Choose Static file or Live API; settings persisted in `localStorage`; “Copy cURL” button.
- **Claims API (Fastify):** `/health`, `/claims/count`, `/claims/list`, `/claims/explain/:id` powered by the claims core; CORS enabled for demos.
- **Docker & Compose:** One command to run API (`:8787`) + static docs (`:8080`).

### Changed
- Monorepo scaffold with **pnpm workspaces**, CI for TS (Vitest) and Rust (cargo).

### Fixed
- N/A

### Security
- Demo CORS policy is permissive by design. Harden before production.

