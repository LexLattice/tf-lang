# @tf-lang/tf-run-wasm

The `tf-run-wasm` package provides a miniature runtime that executes a lightweight
IR payload inside a bundled WebAssembly module. The module delegates control back
to a Node.js host shim so the native and WASM evaluators share the same logic and
can be exercised side-by-side in tests and samples.

## CLI usage

The package ships with a CLI:

```bash
node packages/tf-run-wasm/bin/run-wasm.mjs --help
```

### Flags

- `--ir <file.ir.json>` – run a JSON IR artifact such as
  [`samples/b3/minimal.ir.json`](../../samples/b3/minimal.ir.json).
- `--flow <file.tf>` – compile a toy flow file like
  [`samples/b3/minimal.tf`](../../samples/b3/minimal.tf) into IR before execution.
- `--json` – print the aggregate JSON result to stdout (always newline-terminated).
- `--out <file>` – write the aggregate JSON result to disk (also newline-terminated).
  Parent directories are created automatically.

The CLI exits with code `0` on success and a non-zero code on argument or runtime
errors. All JSON outputs are emitted with a trailing newline and stable key order
so the artifacts are deterministic.

### Examples

Run an existing IR artifact and stream the aggregate JSON result to stdout with a
trailing newline:

```bash
$ node packages/tf-run-wasm/bin/run-wasm.mjs --ir samples/b3/minimal.ir.json --json
{"status":{"ok":true,"engine":"mini-runtime","bytes":170,"primitives":2},"trace":[{"prim_id":"tf:pure/identity@1","effect":"return identity"},{"prim_id":"tf:resource/write-object@1","effect":"persist payload"}]}
```

Compile the sample flow, emit a deterministic summary on stdout, and capture the
aggregate JSON payload on disk (directories are created automatically):

```bash
$ node packages/tf-run-wasm/bin/run-wasm.mjs --flow samples/b3/minimal.tf --out out/mini/result.json
ok engine=mini-runtime primitives=2 bytes=138
$ cat out/mini/result.json
{
  "status": {
    "ok": true,
    "engine": "mini-runtime",
    "bytes": 138,
    "primitives": 2
  },
  "trace": [
    {
      "prim_id": "tf:pure/identity@1",
      "effect": "return identity"
    },
    {
      "prim_id": "tf:resource/write-object@1",
      "effect": "persist payload"
    }
  ]
}
```

The CLI also accepts optional `--status <file>` and `--trace <file>` flags to emit
newline-terminated JSON and JSONL artifacts that mirror the native runtime.

## Programmatic API

The CLI is powered by the `run(opts)` helper exported from the package. Tests can
reuse it to evaluate a pre-parsed IR string or a file on disk while opting into
WASM or native execution explicitly.
