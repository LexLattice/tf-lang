# Track B · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **Discoverability (Expander): The macro expansion logic is a core part of the engine, but there is no direct, documented CLI command to perform L2 to L0 expansion. Developers must find wrapper scripts (`pipeline-expand.mjs`) or infer its usage from tests.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Code Clarity (Expander): The `preprocessL2Yaml` function in `expand.mjs` uses a fragile, stateful loop with regex to wrap multi-line macros in quotes. This is a common source of parsing errors and is hard to debug. A more robust YAML parsing strategy is needed.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Extensibility (Transform Runner): The `runTransform` function is a single, large `switch` statement. Adding new operations requires modifying this central file, which can lead to merge conflicts and makes the code harder to maintain. A more modular, pluggable architecture would be better.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Documentation (Instance Registry): The structure and matching logic of the v2 instance registry are not documented. A contributor would need to read the `resolve.mjs` source to understand how to write rules or what the `default` key means.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.

## Unique to Codex
- **No `tf expand` CLI front-door; contributors must know about bespoke scripts.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Inline comment intolerance breaks the default examples and discourages adding type annotations in YAML.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Domain overrides + plan metadata never persisted back into the L0 JSON, so downstream tools repeat inference.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Decisions applied to .final
- **Discoverability (Expander)**: The macro expansion logic is a core part of the engine, but there is no direct, documented CLI command to perform L2 to L0 expansion. Developers must find wrapper scripts (`pipeline-expand.mjs`) or infer its usage from tests. → documented in ## DX gaps item 1.
- **Code Clarity (Expander)**: The `preprocessL2Yaml` function in `expand.mjs` uses a fragile, stateful loop with regex to wrap multi-line macros in quotes. This is a common source of parsing errors and is hard to debug. A more robust YAML parsing strategy is needed. → documented in ## DX gaps item 2.
- **Extensibility (Transform Runner)**: The `runTransform` function is a single, large `switch` statement. Adding new operations requires modifying this central file, which can lead to merge conflicts and makes the code harder to maintain. A more modular, pluggable architecture would be better. → documented in ## DX gaps item 3.
- **Documentation (Instance Registry)**: The structure and matching logic of the v2 instance registry are not documented. A contributor would need to read the `resolve.mjs` source to understand how to write rules or what the `default` key means. → documented in ## DX gaps item 4.
- No `tf expand` CLI front-door; contributors must know about bespoke scripts. → documented in ## DX gaps item 1.
- Inline comment intolerance breaks the default examples and discourages adding type annotations in YAML. → documented in ## DX gaps item 2.
- Domain overrides + plan metadata never persisted back into the L0 JSON, so downstream tools repeat inference. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.