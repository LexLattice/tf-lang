# @tf-lang/adapter-execution-ts

Deterministic TypeScript execution adapter for TF-Lang specs. It simulates the declarative spec and produces a canonical trace summarising each step.

## Usage

```ts
import { executeSpec } from "@tf-lang/adapter-execution-ts";
import { parseSpec } from "tf-lang-l0";

const spec = parseSpec(await fs.promises.readFile("spec.json", "utf-8"));
const trace = executeSpec(spec);
```

The adapter guarantees:

- stable resource identifiers (`vm-1`, `net-1`, …)
- canonical JSON output (sorted keys, trailing newline)
- error codes prefixed with `E_ADAPTER_*` for unknown operations

Artifacts can be generated with `pnpm --filter @tf-lang/adapter-execution-ts run fixtures`, which emits `out/t2/adapter-ts-trace.json`.
