# tf-check CLI usage

`tf-check` validates TF-Lang specs against the canonical schema. Outputs are deterministic and safe to commit in CI.

## Installation

The CLI ships as part of the workspace. Build it with `pnpm --filter @tf-lang/tf-check run build`.

## Commands

| Command | Description |
| --- | --- |
| `tf-check --help` | print usage and exit |
| `tf-check validate --input <path>` | validate a spec file, writing a canonical JSON result to stdout |
| `tf-check validate --input <path> --out <dir>` | validate and save `result.json` under `<dir>` |
| `tf-check artifacts [--out <dir>]` | emit `help.txt` and `result.json` (defaults to `out/t2/tf-check/`) |

## Exit codes

- `0` – validation succeeded
- `1` – validation failed (spec errors)
- `2` – CLI misuse (missing flags, unknown command, IO errors)

## Result format

Successful runs emit:

```json
{
  "source": { "kind": "file", "path": "fixtures/sample-spec.json" },
  "status": "ok",
  "summary": {
    "name": "demo-plan",
    "version": "0.1",
    "stepCount": 3,
    "operations": {
      "copy": 1,
      "create_network": 1,
      "create_vm": 1
    }
  }
}
```

Failures emit:

```json
{
  "source": { "kind": "file", "path": "bad.json" },
  "status": "error",
  "error": {
    "code": "E_SPEC_OP_UNKNOWN",
    "path": "/steps/0/op",
    "message": "E_SPEC_OP_UNKNOWN /steps/0/op"
  }
}
```

Keys are sorted and the file ends with a newline so repeated runs produce identical bytes.
