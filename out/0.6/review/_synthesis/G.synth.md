# Track G · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **DX (Output Format): The output of `plan-instances` is a dense JSON object. While suitable for machine consumption, it is difficult for a human operator to quickly assess the deployment plan. There is no human-readable summary format (e.g., a table).**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Documentation (Registry v2): The rule-based structure of the v2 instance registry, including how rules are matched and the significance of the `default` key, is entirely undocumented. A developer must read the source code of the resolver (`packages/expander/resolve.mjs`) to understand it.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Missing "Instance Hints": The track is named "Instance Hints & Planning," but there appears to be no mechanism to embed instance hints directly within the L2 or L0 source files. The planning is driven exclusively by the external registry file, which limits per-pipeline customization.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **No "Dry Run" Visualization: The plan is abstract. The `tf graph` command shows the logical DAG, but there is no way to visualize the *physical* instance plan (e.g., color-coding nodes by their assigned instance). This makes it hard to understand the operational topology at a glance.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Unique to Codex
- **No documentation for registry schema (fields, wildcards, precedence) beyond code comments.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Planner output is JSON only; no table/markdown summarizer for release notes.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: release
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Release gating requires this to flip green before cut.
- **Annotated instances are not persisted back into L0 or diagrams, so reviewers cannot see placement decisions without rerunning CLI.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S2
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Decisions applied to .final
- **DX (Output Format)**: The output of `plan-instances` is a dense JSON object. While suitable for machine consumption, it is difficult for a human operator to quickly assess the deployment plan. There is no human-readable summary format (e.g., a table). → documented in ## DX gaps item 1.
- **Documentation (Registry v2)**: The rule-based structure of the v2 instance registry, including how rules are matched and the significance of the `default` key, is entirely undocumented. A developer must read the source code of the resolver (`packages/expander/resolve.mjs`) to understand it. → documented in ## DX gaps item 2.
- **Missing "Instance Hints"**: The track is named "Instance Hints & Planning," but there appears to be no mechanism to embed instance hints directly within the L2 or L0 source files. The planning is driven exclusively by the external registry file, which limits per-pipeline customization. → documented in ## DX gaps item 3.
- **No "Dry Run" Visualization**: The plan is abstract. The `tf graph` command shows the logical DAG, but there is no way to visualize the *physical* instance plan (e.g., color-coding nodes by their assigned instance). This makes it hard to understand the operational topology at a glance. → documented in ## DX gaps item 4.
- No documentation for registry schema (fields, wildcards, precedence) beyond code comments. → documented in ## DX gaps item 1.
- Planner output is JSON only; no table/markdown summarizer for release notes. → documented in ## DX gaps item 2.
- Annotated instances are not persisted back into L0 or diagrams, so reviewers cannot see placement decisions without rerunning CLI. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.