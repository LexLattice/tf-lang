# Track D · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **Release Blocker (Broken Examples): The primary example workflow is broken out of the box. A new contributor running `tasks/run-examples.sh` will immediately hit a fatal error, creating a major onboarding hazard and blocking release.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: release
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Release gating requires this to flip green before cut.
- **DX (Fragile Parser): The root cause of the broken example is the fragile YAML pre-processor that cannot handle inline comments. This was also identified in Track B, but its impact is most visible here.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Documentation (Missing Guidance): There is no `README.md` in `examples/v0.6/` to explain what the examples are, what they demonstrate, or how to run them. A user has to discover the `run-examples.sh` script in a different directory (`tasks/`).**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Diagrams (Tool Dependency): The script's ability to generate user-friendly SVG diagrams depends on the `dot` utility being installed on the system, but this dependency is not documented. If `dot` is missing, only the less accessible `.dot` files are created.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.

## Unique to Codex
- **No README tying the three example commands together or mapping artifacts → docs.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **`tasks/run-examples.sh` fails immediately, so CI-friendly smoke is unavailable.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Monitor spec docs lack explanation of effect expectations (why Outbound/Inbounds appear) beyond the DOT.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.

## Decisions applied to .final
- **Release Blocker (Broken Examples)**: The primary example workflow is broken out of the box. A new contributor running `tasks/run-examples.sh` will immediately hit a fatal error, creating a major onboarding hazard and blocking release. → documented in ## DX gaps item 1.
- **DX (Fragile Parser)**: The root cause of the broken example is the fragile YAML pre-processor that cannot handle inline comments. This was also identified in Track B, but its impact is most visible here. → documented in ## DX gaps item 2.
- **Documentation (Missing Guidance)**: There is no `README.md` in `examples/v0.6/` to explain what the examples are, what they demonstrate, or how to run them. A user has to discover the `run-examples.sh` script in a different directory (`tasks/`). → documented in ## DX gaps item 3.
- **Diagrams (Tool Dependency)**: The script's ability to generate user-friendly SVG diagrams depends on the `dot` utility being installed on the system, but this dependency is not documented. If `dot` is missing, only the less accessible `.dot` files are created. → documented in ## DX gaps item 4.
- No README tying the three example commands together or mapping artifacts → docs. → documented in ## DX gaps item 1.
- `tasks/run-examples.sh` fails immediately, so CI-friendly smoke is unavailable. → documented in ## DX gaps item 2.
- Monitor spec docs lack explanation of effect expectations (why Outbound/Inbounds appear) beyond the DOT. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.