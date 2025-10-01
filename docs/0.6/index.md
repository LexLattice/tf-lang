# TF-Lang v0.6 Pipelines

- [Auto FNOL Fast-Track](pipelines/fnol-fasttrack.md)
- [Auto Quote → Bind → Issue](pipelines/quote-bind-issue.md)
- [Fast-Track 24h SLA Monitors](monitors/fasttrack-24h.md)

# Prover roadmap

- [Lean 4 prover skeleton](../../prover/lean/README.md)

## Law checks

- Run human-readable checks with `tf laws --check <pipeline.l0.json> --goal branch-exclusive` to review PASS/WARN/ERROR entries and any counterexamples found within the boolean bound (`--max-bools N`, default 8).
- Use machine-readable mode with `tf laws --check <pipeline.l0.json> --goal branch-exclusive --json [--policy path] [--caps path]` to feed the same policy/capability inputs as CI and capture structured results.
- `WARN` entries document gaps (e.g., missing metadata or plaintext alongside ciphertext) but do not fail builds; teams can layer stricter policies later if needed.

# TF-Lang v0.6 Specification

> Generated from `spec/v0.6`

> No specification pages were found for this version.
> Tip: add Markdown files under `spec/v0.6` to populate this site.
> For complex macro lines in YAML, prefer block scalars or quotes. The CLI has a best-effort sanitizer, but `--strict-yaml` disables it and enforces standard YAML.

---

[Back to top](#tf-lang-v06-specification)
