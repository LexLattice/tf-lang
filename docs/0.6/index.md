# TF-Lang v0.6 Pipelines

- [Auto FNOL Fast-Track](pipelines/fnol-fasttrack.md)
- [Auto Quote → Bind → Issue](pipelines/quote-bind-issue.md)
- [Fast-Track 24h SLA Monitors](monitors/fasttrack-24h.md)

# TF-Lang v0.6 Specification

> Generated from `spec/v0.6`

> No specification pages were found for this version.
> Tip: add Markdown files under `spec/v0.6` to populate this site.
> For complex macro lines in YAML, prefer block scalars or quotes. The CLI has a best-effort sanitizer, but `--strict-yaml` disables it and enforces standard YAML.

---

## Macro laws

- `state.merge@crdt.gcounter` – associative, commutative, idempotent merge of grow-only counters.
- `process.retry` – retry-safe when the wrapped RPC produces a stable `corr` (idempotent-by-corr).

---

[Back to top](#tf-lang-v06-specification)
