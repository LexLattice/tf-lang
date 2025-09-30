# @tf-lang/tf-run-wasm

`@tf-lang/tf-run-wasm` dynamically loads the `tf-eval-wasm` bindings when they are
available and falls back to a deterministic stub evaluator otherwise. The stub is
also used when the environment variable `TF_RUN_WASM_DISABLE_WASM=1` is set.

`run(opts)` returns a status summary and a normalized trace:

```ts
interface EvalStatus { ok: boolean; engine: string; bytes: number; }
interface EvalTraceItem { prim_id?: string; effect?: string; }
interface EvalResult { status: EvalStatus; trace: EvalTraceItem[]; }
```

Status JSON files are formatted with two-space indentation and a trailing newline.
Trace files are emitted as newline-terminated JSONL where every trace entry is
written on its own line.

## CLI

The package ships with a thin CLI wrapper that operates on IR JSON files. A
minimal example creates a temporary directory, writes a tiny IR file, and runs
the CLI to produce status and trace artifacts:

```bash
TMP_DIR="$(mktemp -d)"
cat <<'JSON' > "$TMP_DIR/sample.ir.json"
{ "primitives": ["tf:pure/identity@1"] }
JSON

tf-run-wasm --ir "$TMP_DIR/sample.ir.json" \
  --status "$TMP_DIR/status.json" \
  --trace "$TMP_DIR/trace.jsonl"

cat "$TMP_DIR/status.json"
cat "$TMP_DIR/trace.jsonl"
```

The command exits with `0` when evaluation succeeds. It writes the optional status
and trace files when the corresponding flags are provided and reports argument or
runtime errors on stderr. Set `TF_RUN_WASM_DISABLE_WASM=1` to force the stub
evaluator even when the WebAssembly bindings are available.
