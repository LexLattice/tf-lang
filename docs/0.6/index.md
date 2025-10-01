# TF-Lang v0.6 Pipelines

- [Auto FNOL Fast-Track](pipelines/fnol-fasttrack.md)
- [Auto Quote → Bind → Issue](pipelines/quote-bind-issue.md)
- [Fast-Track 24h SLA Monitors](monitors/fasttrack-24h.md)

## Tools

- `tf plan-instances <L0>` summarizes instance hints by domain and channel scheme; use `--registry` to simulate different deployments.

# TF-Lang v0.6 Specification

> Generated from `spec/v0.6`

> No specification pages were found for this version.
> Tip: add Markdown files under `spec/v0.6` to populate this site.
> For complex macro lines in YAML, prefer block scalars or quotes. The CLI has a best-effort sanitizer, but `--strict-yaml` disables it and enforces standard YAML.

---

## Macro laws

- `state.merge@jsonpatch` – order-sensitive; no algebraic laws; root ops unsupported by design.
- `state.merge@crdt.gcounter` – associative, commutative, idempotent (reported per-node).
- `process.retry` – retry-safe when the wrapped RPC produces a stable `corr` (idempotent-by-corr).

Auth tokens are minted as `base58(blake3 bytes)` of the canonical payload (secret + claims + alg).

---

[Back to top](#tf-lang-v06-specification)

## Tools

### `tf typecheck`

Run `tf typecheck <L0_FILE> [--adapters <registry.json>]` to infer port types across an L0 DAG.
The command exits `0` when all bindings match (including cases where adapters are suggested),
`1` when blocking mismatches remain, and `2` for usage errors. Use `--adapters` to point at a
custom adapter registry; otherwise `adapters/registry.json` is loaded.

Adapter suggestions are reported inline:

```
OK with 1 suggestion(s)
- T_needs_json in.payload.claim from @fnol_csv:
  FnolV1 (csv) → FnolV1 (json) (use Transform(op: adapter.fnol_csv_to_json))
```

## Capabilities

Capability allow lists may now include wildcard entries (e.g. `cap:keypair:*`).
Any required capability matching that pattern is treated as satisfied when computing the checker report.
