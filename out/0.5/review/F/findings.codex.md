# Track F Findings (Top 10)

1. **S3 · C2** — Release artifacts are non-deterministic because `pack-all` writes `generated_at: new Date().toISOString()`. Evidence: `tools/release/pack-all.mjs` lines 200-214. **Repro:** run the script twice; diffs show only timestamp changes. **Fix sketch:** accept a `--generated-at` override or omit the field. **Risk if deferred:** reproducibility checks fail and caches miss on every run.

2. **S3 · C2** — `scripts/docs/build.mjs` also embeds a fresh timestamp, so doc bundles are never identical. Evidence: `scripts/docs/build.mjs` lines 24-35. **Fix sketch:** reuse the same deterministic timestamp used in release metadata. **Risk if deferred:** doc artifacts can’t be cached or diffed cleanly.

3. **S3 · C1** — `pack-all` emits package entries in the discovery order of the allowlist; when `PACK_ROOTS` differs across invocations the output ordering changes. Evidence: `tools/release/pack-all.mjs` lines 126-198. **Fix sketch:** sort `packages` by manifest path before serialising. **Risk if deferred:** downstream tooling sees noisy diffs depending on env vars.

4. **S4 · C2** — `lockfile-guard`’s `--json` flag is ineffective; `emit` prints the same JSON blob regardless. Evidence: `tools/ci/lockfile-guard.mjs` lines 20-24. **Repro:** run with and without `--json`; outputs identical. **Fix sketch:** provide a human-readable branch (e.g., formatted hint) when `--json` is false. **Risk if deferred:** flag consumers assume they’re getting structured output when they’re not.

5. **S3 · C1** — `pack-all` doesn’t verify that `pnpm pack` honoured `private: false`; if a package flips to private mid-run, the artifact still lands in the manifest. Evidence: `tools/release/pack-all.mjs` lines 150-196. **Fix sketch:** filter results by `manifest.private !== true` after reading the manifest from disk, not before packing. **Risk if deferred:** accidental publication of private packages.

6. **S3 · C2** — `pack-all` invokes `pnpm pack` without `--ignore-scripts`, so packages with heavy `prepack` hooks slow releases. Evidence: `tools/release/pack-all.mjs` lines 162-176. **Fix sketch:** add `--ignore-scripts` and run necessary build steps earlier in CI. **Risk if deferred:** release dry-runs execute arbitrary user hooks.

7. **S3 · C1** — Release workflow only runs on Ubuntu Node 20. Evidence: `.github/workflows/release.yml` lines 10-32. **Fix sketch:** add Windows/macOS runners and Node LTS to ensure cross-platform parity. **Risk if deferred:** release scripts may break on other environments unnoticed.

8. **S4 · C2** — Composite `setup-pnpm` always runs `pnpm install` when `install=='true'`, even if the repo already ran install earlier in the job, wasting minutes. Evidence: `.github/actions/setup-pnpm/action.yml` lines 31-54. **Fix sketch:** allow callers to skip install entirely (`install: ''`) or respect an env flag. **Risk if deferred:** redundant installs slow CI.

9. **S4 · C1** — `docs/build` and `lockfile-guard` share identical CLI scaffolding but duplicate code; divergence risks inconsistent behaviour. Evidence: `scripts/docs/build.mjs` and `tools/ci/lockfile-guard.mjs`. **Fix sketch:** extract a shared `emitJsonStatus` helper in `tools/_cli`. **Risk if deferred:** future fixes must be duplicated manually.

10. **S3 · C2** — `pack-all` computes checksums over the JSON manifest, not the tarballs themselves, so tampering with `.tgz` outputs downstream goes undetected. Evidence: `tools/release/pack-all.mjs` lines 205-214. **Fix sketch:** hash each artifact (`sha256sum`) and include in the payload. **Risk if deferred:** release verification lacks real integrity checks.
