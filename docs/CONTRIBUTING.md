# Contributing

## Release helpers

The release tooling lives under `tools/release/` and each script emits structured JSON for CI.

- **Pack manifest** – `node tools/release/pack-all.mjs [--out path] [--verbose]`
  - Generates `out/0.5/release/pack.json` and prints a status blob containing the checksum and package count.
- **Changelog draft** – `node tools/release/changelog.mjs [--range A..B] [--out path]`
  - Produces `out/0.5/release/CHANGELOG.next.md` by scanning the git log using Conventional Commit prefixes.
- **Snapshot lanes** – `node tools/release/snapshot-lanes.mjs --tag <lane> [--out path]`
  - Summarizes release lanes from the pack manifest so CI jobs can publish dry-run metadata without mutation.

Each CLI supports `--help` for usage, `--quiet` to silence stdout, and `--verbose` (or `RELEASE_VERBOSE=1`) to mirror progress steps to stderr. Artifacts written via `--out` are formatted JSON with trailing newlines for deterministic diffs.
