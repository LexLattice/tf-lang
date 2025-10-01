# Track A · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **DX Friction (CLI): Commands are verbose (`node tools/tf-lang-cli/index.mjs ...`). The `pnpm install` log shows warnings that shorter aliases (e.g., `tf-plan`) failed to be created, indicating a broken or incomplete setup in `package.json`.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Documentation (Onboarding): The root `README.md` is for v0.5 and does not reflect the v0.6 tools and examples. This creates immediate confusion for new contributors.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Documentation (Gaps): `docs/0.6/index.md` explicitly states that detailed v0.6 specification pages are missing. There is no central `CONTRIBUTING.md` to guide new developers on workflow, setup, and testing.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Schema Versioning: The presence of v0.4 schemas alongside current schemas in `schemas/` can lead to confusion about which to reference.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Unique to Codex
- **Schema + docs drift from 0.6 kernel shape (structured transform inputs, monitors bundle) blocks validation + onboarding.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S2
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Quickstart script fails out-of-the-box; no happy path to see a green build.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **`docs/0.6/index.md` references empty spec and lacks per-track gate summaries.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.

## Decisions applied to .final
- **DX Friction (CLI)**: Commands are verbose (`node tools/tf-lang-cli/index.mjs ...`). The `pnpm install` log shows warnings that shorter aliases (e.g., `tf-plan`) failed to be created, indicating a broken or incomplete setup in `package.json`. → documented in ## DX gaps item 1.
- **Documentation (Onboarding)**: The root `README.md` is for v0.5 and does not reflect the v0.6 tools and examples. This creates immediate confusion for new contributors. → documented in ## DX gaps item 2.
- **Documentation (Gaps)**: `docs/0.6/index.md` explicitly states that detailed v0.6 specification pages are missing. There is no central `CONTRIBUTING.md` to guide new developers on workflow, setup, and testing. → documented in ## DX gaps item 3.
- **Schema Versioning**: The presence of v0.4 schemas alongside current schemas in `schemas/` can lead to confusion about which to reference. → documented in ## DX gaps item 4.
- Schema + docs drift from 0.6 kernel shape (structured transform inputs, monitors bundle) blocks validation + onboarding. → documented in ## DX gaps item 1.
- Quickstart script fails out-of-the-box; no happy path to see a green build. → documented in ## DX gaps item 2.
- `docs/0.6/index.md` references empty spec and lacks per-track gate summaries. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.