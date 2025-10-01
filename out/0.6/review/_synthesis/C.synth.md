# Track C · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **Code Duplication (Runtime): The L0 runtime (`packages/runtime/run.mjs`) re-implements the entire `Transform` logic, creating a near-exact copy of the `runTransform` function in `packages/transform/index.mjs`. This is a critical maintenance and correctness hazard.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S1
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Discoverability (Runtime): There is no CLI command to execute an L0 file directly. This makes it difficult for developers to test or debug the runtime behavior of a compiled pipeline without writing a custom script.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **DX (Checker): The checker's output is a monolithic `TFREPORT.json` file. While comprehensive, it can be hard to quickly parse for the specific cause of a failure. A human-readable summary output to the console would improve the user experience.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Documentation (Z3 Harness): The Z3 integration is a powerful feature, but its mechanism, prerequisites (is Z3 bundled or a system dependency?), and how to write new Z3-backed laws are entirely undocumented.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.

## Unique to Codex
- **No runtime harness to execute L0 pipelines against the memory bus; only checker + specs exist.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Checker lacks per-rule exit codes (always exit 0), so CI integration must parse JSON manually.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Law coverage is shallow: branch exclusivity/monotonic/confidential only produce PASS/NEUTRAL; no counterexample emission wired into CLI output.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Decisions applied to .final
- **Code Duplication (Runtime)**: The L0 runtime (`packages/runtime/run.mjs`) re-implements the entire `Transform` logic, creating a near-exact copy of the `runTransform` function in `packages/transform/index.mjs`. This is a critical maintenance and correctness hazard. → documented in ## DX gaps item 1.
- **Discoverability (Runtime)**: There is no CLI command to execute an L0 file directly. This makes it difficult for developers to test or debug the runtime behavior of a compiled pipeline without writing a custom script. → documented in ## DX gaps item 2.
- **DX (Checker)**: The checker's output is a monolithic `TFREPORT.json` file. While comprehensive, it can be hard to quickly parse for the specific cause of a failure. A human-readable summary output to the console would improve the user experience. → documented in ## DX gaps item 3.
- **Documentation (Z3 Harness)**: The Z3 integration is a powerful feature, but its mechanism, prerequisites (is Z3 bundled or a system dependency?), and how to write new Z3-backed laws are entirely undocumented. → documented in ## DX gaps item 4.
- No runtime harness to execute L0 pipelines against the memory bus; only checker + specs exist. → documented in ## DX gaps item 1.
- Checker lacks per-rule exit codes (always exit 0), so CI integration must parse JSON manually. → documented in ## DX gaps item 2.
- Law coverage is shallow: branch exclusivity/monotonic/confidential only produce PASS/NEUTRAL; no counterexample emission wired into CLI output. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.