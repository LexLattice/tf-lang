# Track F · synthesis

## Overlapping issues
- (none)

## Unique to Jules
- **DX (No Autofix/Codegen for Adapters): The typechecker can *suggest* an adapter is needed but provides no way to automatically apply it. A developer must manually insert a new `Transform` node into the L0 file with the correct `spec.op`. This is tedious, error-prone, and requires manual editing of a generated file, which `AGENTS.md` discourages.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Documentation (Port Typing Syntax): The syntax for defining port types in the `metadata.port_types` block is complex and undocumented. Features like wildcard (`*`) and default ports are used in the typechecker logic but are not explained anywhere.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S2
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **Incompleteness (Capability Lattice): The capability lattice in `policy/capability.lattice.json` only covers `rpc:*` channels. Other channels used in the examples (e.g., `metric:*`, `policy:enforce`) are not defined, meaning the checker will not derive any required capabilities for them. This creates a security and policy blind spot.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **Code Clarity (Type Descriptor Logic): The typechecker contains multiple functions (`normalizeDescriptor`, `extractDescriptor`, `selectNext`) with complex, overlapping logic for parsing and resolving type descriptors. This code is hard to follow and maintain.**
  - Evidence: docs.jules.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Unique to Codex
- **No documentation of schemaRef catalogue (what does `AutoQuoteOfferV2` mean?); authors must guess.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: docs
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Onboarding depends on aligned documentation, so the gap remains visible.
- **`tf typecheck` lacks `--json` output, making CI parsing hard.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.
- **No canned adapter scaffolding script; adding adapters is manual JSON editing.**
  - Evidence: docs.codex.md §Gaps
  - Severity: S3
  - Area: dx
  - Relevance (confirm): Still impacts v0.6 workflows with no documented remediation. Developer workflows continue to encounter the described friction.

## Decisions applied to .final
- **DX (No Autofix/Codegen for Adapters)**: The typechecker can *suggest* an adapter is needed but provides no way to automatically apply it. A developer must manually insert a new `Transform` node into the L0 file with the correct `spec.op`. This is tedious, error-prone, and requires manual editing of a generated file, which `AGENTS.md` discourages. → documented in ## DX gaps item 1.
- **Documentation (Port Typing Syntax)**: The syntax for defining port types in the `metadata.port_types` block is complex and undocumented. Features like wildcard (`*`) and default ports are used in the typechecker logic but are not explained anywhere. → documented in ## DX gaps item 2.
- **Incompleteness (Capability Lattice)**: The capability lattice in `policy/capability.lattice.json` only covers `rpc:*` channels. Other channels used in the examples (e.g., `metric:*`, `policy:enforce`) are not defined, meaning the checker will not derive any required capabilities for them. This creates a security and policy blind spot. → documented in ## DX gaps item 3.
- **Code Clarity (Type Descriptor Logic)**: The typechecker contains multiple functions (`normalizeDescriptor`, `extractDescriptor`, `selectNext`) with complex, overlapping logic for parsing and resolving type descriptors. This code is hard to follow and maintain. → documented in ## DX gaps item 4.
- No documentation of schemaRef catalogue (what does `AutoQuoteOfferV2` mean?); authors must guess. → documented in ## DX gaps item 1.
- `tf typecheck` lacks `--json` output, making CI parsing hard. → documented in ## DX gaps item 2.
- No canned adapter scaffolding script; adding adapters is manual JSON editing. → documented in ## DX gaps item 3.

---

**Sources considered:** docs.jules.md, docs.codex.md

**Dead links fixed:** (pending verification)

**Open questions:**
- Need follow-up validation once quickstarts are stable.