# tf-check — Usage

`tf-check` validates TF-Lang artifacts and emits deterministic JSON results.

## Commands
- `tf-check --help` → prints usage to stdout (CI captures to `out/t2/tf-check/help.txt`).
- `tf-check validate --input <path>` → validates files under `<path>` and writes `out/t2/tf-check/result.json`.

## Exit codes
- `0` success, `1` validation error, `2` usage error.

## Determinism
- No network, no timestamps in output.
- Canonical JSON encoding; stable key order.
- Seeds recorded for randomized checks (if any).
