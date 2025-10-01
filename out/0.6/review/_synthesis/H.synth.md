# Track H · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **DX (Opaque Prover): The Z3 prover is a critical component, but it's treated like a black box. There is no documentation on how it's invoked, what SMT-LIB code is generated, or how to debug it. The error `solver-failed` provides no actionable information.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S1
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Incompleteness (Shallow Law Checks): The `monotonic_log` and `confidential_envelope` checks are shallow pattern matches, not deep proofs. They check for the *presence* of a certain publish event but don't verify the *content* or *logic* (e.g., that the log is actually append-only, or that plaintext is never exposed alongside ciphertext). This provides a false sense of security.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Documentation (Goals): The `tf laws` command requires a `--goal` argument, but there is no way to list the available goals. A user must find them by reading the source code or documentation.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **DX (Noisy Counterexamples): The counterexample format is useful but could be improved. It doesn't explicitly state which L0 nodes are in conflict, instead listing all nodes in the positive and negative paths, which can be verbose.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Unique to Codex
- **No CLI exposes counterexample JSON directly; branch exclusivity NEUTRAL gives no insight into guard coverage.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Confidential envelope + monotonic log rely on heuristics, not solver-backed proofs; WARNs never fail builds, weakening compliance story.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **No docs describing how to author custom law goals or interpret prover payloads.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.

## Decisions applied to .final
- **DX (Opaque Prover)**: The Z3 prover is a critical component, but it's treated like a black box. There is no documentation on how it's invoked, what SMT-LIB code is generated, or how to debug it. The error `solver-failed` provides no actionable information. → documented in ## DX gaps item 1.
- **Incompleteness (Shallow Law Checks)**: The `monotonic_log` and `confidential_envelope` checks are shallow pattern matches, not deep proofs. They check for the *presence* of a certain publish event but don't verify the *content* or *logic* (e.g., that the log is actually append-only, or that plaintext is never exposed alongside ciphertext). This provides a false sense of security. → documented in ## DX gaps item 2.
- **Documentation (Goals)**: The `tf laws` command requires a `--goal` argument, but there is no way to list the available goals. A user must find them by reading the source code or documentation. → documented in ## DX gaps item 3.
- **DX (Noisy Counterexamples)**: The counterexample format is useful but could be improved. It doesn't explicitly state which L0 nodes are in conflict, instead listing all nodes in the positive and negative paths, which can be verbose. → documented in ## DX gaps item 4.
- No CLI exposes counterexample JSON directly; branch exclusivity NEUTRAL gives no insight into guard coverage. → documented in ## DX gaps item 1.
- Confidential envelope + monotonic log rely on heuristics, not solver-backed proofs; WARNs never fail builds, weakening compliance story. → documented in ## DX gaps item 2.
- No docs describing how to author custom law goals or interpret prover payloads. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.