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
minimal example writes a small IR file, runs the CLI, and inspects the outputs:

```bash
echo '{"primitives":[{"prim_id":"tf:pure/identity@1"}]}' > /tmp/run.ir.json
tf-run-wasm --ir /tmp/run.ir.json --status /tmp/status.json --trace /tmp/trace.jsonl
cat /tmp/status.json
cat /tmp/trace.jsonl
```

When files are written the CLI emits a deterministic `wrote …` line such as
`wrote status=true trace=true steps=1`. Passing `--json` (or omitting file
targets) prints a single-line JSON summary with the execution result:

```bash
tf-run-wasm --ir /tmp/run.ir.json --json
# {"ok":true,"status_written":false,"trace_written":false,"steps":1}
```

Environment flags:

* `TF_RUN_WASM_DISABLE_WASM=1` — force the stub evaluator even when the
  WebAssembly bindings are available.
* `TF_RUN_WASM_DEBUG=1` — emit debug warnings to stderr (never stdout).
