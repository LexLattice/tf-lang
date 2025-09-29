# @tf-lang/tf-trace

The `@tf-lang/tf-trace` package contains the trace schema, ingest utilities, and the `tf-trace` CLI used by the C-Trace-Perf block.

## Trace schema

Trace records are JSON objects with the following fields:

- `ts` (number, required): monotonically increasing timestamp.
- `prim_id` (string, required): identifier of the primitive being measured.
- `effect` (string, required): effect bucket (`cpu`, `io`, etc.).
- `ms` (number, optional): elapsed milliseconds for the record. When provided it must be non-negative.

The schema is published at [`src/schema/trace.schema.json`](./src/schema/trace.schema.json).

## Budget specification

Budget files are JSON objects with these keys:

- `total_ms_max` (number, optional): cap on total milliseconds across the trace summary.
- `by_effect` (object, optional): map of effect name to constraint object. Each constraint may provide:
  - `ms_max` (number, optional): per-effect cap on milliseconds.
  - `count_max` (number, optional): per-effect cap on record count.

Unknown keys are rejected by the CLI. See [`samples/c/budgets.sample.json`](../../samples/c/budgets.sample.json) for an example.

## CLI

Run `pnpm -C packages/tf-trace build` to compile the TypeScript sources, then invoke the CLI via `node packages/tf-trace/bin/trace.mjs` or the workspace binary `tf-trace`.

Use `tf-trace --help` to see the available commands and options. All commands emit a single JSON line on stdout describing the status. Diagnostics are sent to stderr.
