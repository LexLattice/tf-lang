# Agents — T2 Runtime & Tooling Epic (Addendum)

This addendum extends `agents.md` for T2 tasks (runtime adapters, CLI, mapping, coverage).

**Mission:** Ship the *runtime + tooling* foundation that lets us validate TF-Lang artifacts end‑to‑end:
- **T2_1**: `tf-check` CLI (TS)
- **T2_2**: Execution Adapters (TS + Rust)
- **T2_3**: Trace→Tags mapper (TS)
- **T2_4**: Coverage generator (TS) — depends on T2_3
- **T2_5**: CI wiring jobs (matrix)

**Fences (inherit from agents.md):** no network; deterministic; canonical JSON; no runtime deps (dev only); TS: no deep imports, internal ESM imports end with `.js`, no `as any`; Rust: no `static mut`, no panicking unwraps in libs.

**Artifacts (must exist for CI green):**
- `out/t2/tf-check/help.txt`, `out/t2/tf-check/result.json`
- `out/t2/trace-tags.json` (mapper)
- `out/t2/coverage.json`, `out/t2/coverage.html`
- Adapter parity proof (if both runtimes implemented): `out/t2/adapter-parity.json`

**PR Body:** Every PR for this epic MUST follow `.github/pull_request_template.md`.
