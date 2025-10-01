# Track E · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **Release Blocker (Disconnected Law Checking): The law verification system is fundamentally flawed. The `state.merge` macro attaches law IDs to L0 nodes, but the corresponding law checker (`laws/crdt-merge.mjs`) does not read or use them. Instead, it runs a few hardcoded, static examples. This creates a dangerous illusion of verification; the system is not actually checking the algebraic properties of the code being submitted.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Missing Macros (Auth): The track scope includes `auth` macros, but they are not implemented in the expander. While `auth.*` *operations* exist in the transform layer, they are not exposed as first-class L1 macros, making them inaccessible from L2 pipelines.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Documentation (Law System): The mechanism for attaching laws and the process for creating a new law checker are completely undocumented. It's unclear how a contributor would add verification for a new algebraic property.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Inconsistent Naming (await): The `process.await.any` and `process.await.all` macros accept `sources`, `targets`, or `inputs` as the key for the array of events to wait for. This inconsistency is confusing and should be standardized to a single key (e.g., `sources`).**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Unique to Codex
- **No macro reference doc for `policy.enforce`, `process.saga`, or `state.diff`; teams must read source to understand inputs/outputs.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Law suite lacks coverage for policy dominance, saga monotonicity, or `process.await` exclusivity.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **CRDT/jsonpatch notes live in code comments; docs do not surface example payloads or invariants.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.

## Decisions applied to .final
- **Release Blocker (Disconnected Law Checking)**: The law verification system is fundamentally flawed. The `state.merge` macro attaches law IDs to L0 nodes, but the corresponding law checker (`laws/crdt-merge.mjs`) **does not read or use them**. Instead, it runs a few hardcoded, static examples. This creates a dangerous illusion of verification; the system is not actually checking the algebraic properties of the code being submitted. → documented in ## DX gaps item 1.
- **Missing Macros (Auth)**: The track scope includes `auth` macros, but they are not implemented in the expander. While `auth.*` *operations* exist in the transform layer, they are not exposed as first-class L1 macros, making them inaccessible from L2 pipelines. → documented in ## DX gaps item 2.
- **Documentation (Law System)**: The mechanism for attaching laws and the process for creating a new law checker are completely undocumented. It's unclear how a contributor would add verification for a new algebraic property. → documented in ## DX gaps item 3.
- **Inconsistent Naming (await)**: The `process.await.any` and `process.await.all` macros accept `sources`, `targets`, or `inputs` as the key for the array of events to wait for. This inconsistency is confusing and should be standardized to a single key (e.g., `sources`). → documented in ## DX gaps item 4.
- No macro reference doc for `policy.enforce`, `process.saga`, or `state.diff`; teams must read source to understand inputs/outputs. → documented in ## DX gaps item 1.
- Law suite lacks coverage for policy dominance, saga monotonicity, or `process.await` exclusivity. → documented in ## DX gaps item 2.
- CRDT/jsonpatch notes live in code comments; docs do not surface example payloads or invariants. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.