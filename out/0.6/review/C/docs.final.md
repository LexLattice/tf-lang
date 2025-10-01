# Track C · Runtime & Checker

## What exists now
- **Runtime / Executor**: An L0 DAG executor is implemented in `packages/runtime/run.mjs`. It processes an L0 file's `nodes` array, simulates `Publish` and `Subscribe` events using an in-memory message bus (`bus.memory.mjs`), and executes `Transform` and `Keypair` primitives. It can be seeded with initial events and supports custom handlers for specific channels.
- **Checker**: The core checker (`packages/checker/check.mjs`) is a comprehensive static analysis tool. It verifies: **Effects**: Compares declared vs. computed effects (`Outbound`, `Inbound`, `Entropy`, `Pure`). **Policy**: Ensures all `Publish`/`Subscribe` channels are in a configurable allow-list (`policy/policy.allow.json`). **Capabilities**: Matches required capabilities (e.g., `cap:publish:rpc:req:*`) against a provided list, using a lattice (`policy/capability.lattice.json`) to derive requirements. **Laws**: Orchestrates checks for algebraic laws (idempotency, CRDT properties) and logical properties (RPC pairing, branch exclusivity).
- **Z3 Harness**: The checker integrates with the Z3 prover via modules in the `laws/` directory. For example, `laws/branch_exclusive.mjs` parses `when` clauses, identifies branches, and calls the Z3 harness (`packages/prover/z3.mjs`) to prove that positive and negative branches are mutually exclusive.
- **Deterministic runtime core** (`packages/runtime/run.mjs`): in-memory bus, transform evaluator covering JSON schema validation, hashing, CRDT merges, policy eval, auth token mint/check, time alignment, saga planning.
- **Checker CLI** (`packages/checker/check.mjs`): evaluates declared vs computed effects, policy allowlists, capability lattice requirements, RPC pairing, idempotency via Z3, CRDT merge coverage, monotonic log + confidential envelope heuristics.
- **`tf laws --check`**: friendly wrapper for branch exclusivity/monotonic/confidential goals with JSON or console output.
- **Monitoring utilities**: `scripts/assert-kernel-only.mjs` and example spec scripts assert RPC pairing, PII guardrails, effect summaries for monitors.

## How to run (10-minute quickstart)
1. **Run the Checker on an L0 file**.
```bash
node packages/checker/check.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --out out/0.6/review/C/TFREPORT.json
```
2. **Run the L0 Executor (Runtime)**: The runtime is a library function (`executeL0`) and not exposed directly as a CLI command. It is used in tests and other scripts. A conceptual example.
```bash
// import { executeL0 } from 'packages/runtime/run.mjs';
```
```bash
// const l0 = JSON.parse(fs.readFileSync('...'));
```
```bash
// const { trace } = await executeL0(l0);
```
3. Run command.
```bash
node packages/checker/check.mjs \
```
```bash
examples/v0.6/build/auto.quote.bind.issue.v2.l0.json \
```
```bash
--policy policy/policy.allow.json \
```
```bash
--caps policy/policy.allow.json \
```
```bash
--out out/quote.bind.issue.report.json
```
```bash
node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.quote.bind.issue.v2.l0.json --max-bools 4
```
4. Inspect out/*.json for RED/AMBER gates; the checker is deterministic (sorted arrays, ISO timestamp).
```bash
out/*.json
```

## Common errors & fixes
| Symptom | Probable cause | Fix |
| --- | --- | --- |
| `Checker reports status: RED` | One or more checks failed (e.g., an effect was missing, a channel was not in the policy, or a law was violated). | Inspect the generated `TFREPORT.json` file. The detailed report will pinpoint the exact failure under `effects`, `policy`, `capabilities`, or `laws`. |
| `unsupported node kind: <KIND>` | The L0 file contains a node kind that the runtime executor in `run.mjs` does not recognize. | Add the necessary logic to the `executeL0` function to handle the new node kind. |
| **Missing capability manifest** → checker status RED even when policy passes. Fix by pointing `--caps` to an allowlist JSON (same shape as `policy.allow.json`) or generate `out/caps.json` listing granted caps. | Investigate root cause | Document mitigation |
| **Idempotency RED** on RPC publishes stems from macros that hash entropy-bearing bodies without stable seeds. For demos mark as known gap; long-term fix is to ensure `corr` derives from deterministic inputs or wrap in `process.retry` with saga key. | Investigate root cause | Document mitigation |
| Z3 optional dep** | first solver call downloads a wasm; ensure `pnpm install` succeeded. If offline, expect `solver-failed` reasons — document as WARN, not blocker. | first solver call downloads a wasm; ensure `pnpm install` succeeded. If offline, expect `solver-failed` reasons — document as WARN, not blocker. |

## Acceptance gates & signals
| Gate | Command | Success signal |
| --- | --- | --- |
| **Run the Checker on an L0 file** | `node packages/checker/check.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json --out out/0.6/review/C/TFREPORT.json` | Command succeeds without errors. |
| **Run the L0 Executor (Runtime)**: The runtime is a library function (`executeL0`) and not exposed directly as a CLI command. It is used in tests and other scripts. A conceptual example | `// import { executeL0 } from 'packages/runtime/run.mjs';` | Command succeeds without errors. |
| **Run the L0 Executor (Runtime)**: The runtime is a library function (`executeL0`) and not exposed directly as a CLI command. It is used in tests and other scripts. A conceptual example | `// const l0 = JSON.parse(fs.readFileSync('...'));` | Command succeeds without errors. |
| **Run the L0 Executor (Runtime)**: The runtime is a library function (`executeL0`) and not exposed directly as a CLI command. It is used in tests and other scripts. A conceptual example | `// const { trace } = await executeL0(l0);` | Command succeeds without errors. |
| Run command | `node packages/checker/check.mjs \` | Command succeeds without errors. |
| Run command | `examples/v0.6/build/auto.quote.bind.issue.v2.l0.json \` | Command succeeds without errors. |
| Run command | `--policy policy/policy.allow.json \` | Command succeeds without errors. |
| Run command | `--caps policy/policy.allow.json \` | Command succeeds without errors. |
| Run command | `--out out/quote.bind.issue.report.json` | Command succeeds without errors. |
| Run command | `node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.quote.bind.issue.v2.l0.json --max-bools 4` | Command succeeds without errors. |
| Inspect out/*.json for RED/AMBER gates; the checker is deterministic (sorted arrays, ISO timestamp) | `out/*.json` | Command succeeds without errors. |

## DX gaps
- **Code Duplication (Runtime)**: The L0 runtime (`packages/runtime/run.mjs`) re-implements the entire `Transform` logic, creating a near-exact copy of the `runTransform` function in `packages/transform/index.mjs`. This is a critical maintenance and correctness hazard.
- **Discoverability (Runtime)**: There is no CLI command to execute an L0 file directly. This makes it difficult for developers to test or debug the runtime behavior of a compiled pipeline without writing a custom script.
- **DX (Checker)**: The checker's output is a monolithic `TFREPORT.json` file. While comprehensive, it can be hard to quickly parse for the specific cause of a failure. A human-readable summary output to the console would improve the user experience.
- **Documentation (Z3 Harness)**: The Z3 integration is a powerful feature, but its mechanism, prerequisites (is Z3 bundled or a system dependency?), and how to write new Z3-backed laws are entirely undocumented.
- No runtime harness to execute L0 pipelines against the memory bus; only checker + specs exist.
- Checker lacks per-rule exit codes (always exit 0), so CI integration must parse JSON manually.
- Law coverage is shallow: branch exclusivity/monotonic/confidential only produce PASS/NEUTRAL; no counterexample emission wired into CLI output.

## Top issues (synthesized)
- **Code Duplication (Runtime)**: The L0 runtime (`packages/runtime/run.mjs`) re-implements the entire `Transform` logic, creating a near-exact copy of the `runTransform` function in `packages/transform/index.mjs`. This is a critical maintenance and correctness hazard.
- **Discoverability (Runtime)**: There is no CLI command to execute an L0 file directly. This makes it difficult for developers to test or debug the runtime behavior of a compiled pipeline without writing a custom script.
- **DX (Checker)**: The checker's output is a monolithic `TFREPORT.json` file. While comprehensive, it can be hard to quickly parse for the specific cause of a failure. A human-readable summary output to the console would improve the user experience.

## Next 3 improvements
- **Refactor the Runtime to eliminate duplicated Transform logic** — Action: Remove the `evaluateTransform` function from `packages/runtime/run.mjs` and have it import and use `runTransform` from `packages/transform/index.mjs` instead; Impact: Critical. Eliminates a major source of code duplication, reducing bugs and maintenance overhead; Effort: Small
- **Create a `tf run` command to execute L0 files** — Action: Add a `run` command to the main CLI (`tools/tf-lang-cli/index.mjs`) that wraps the `executeL0` function, allowing a user to run an L0 file and see the resulting trace output; Impact: High. Makes the runtime discoverable and provides a direct way to test and observe pipeline execution; Effort: Medium
- **Add a human-readable summary to the Checker's output** — Action: When not in a `--json` mode, the checker should print a concise summary of the results to `stdout`, highlighting which sections failed (e.g., "Effects: FAILED", "Laws (idempotency): PASSED"); Impact: High. Improves the developer feedback loop by making it much faster to diagnose failures; Effort: Medium

## References
- [packages/runtime/run.mjs](../../../../packages/runtime/run.mjs)
- [packages/checker/check.mjs](../../../../packages/checker/check.mjs)
- [policy/policy.allow.json](../../../../policy/policy.allow.json)
- [policy/capability.lattice.json](../../../../policy/capability.lattice.json)
- [laws/branch_exclusive.mjs](../../../../laws/branch_exclusive.mjs)
- [packages/prover/z3.mjs](../../../../packages/prover/z3.mjs)
- [examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json](../../../../examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json)
- [packages/transform/index.mjs](../../../../packages/transform/index.mjs)
- [tools/tf-lang-cli/index.mjs](../../../../tools/tf-lang-cli/index.mjs)
- [scripts/assert-kernel-only.mjs](../../../../scripts/assert-kernel-only.mjs)
- [examples/v0.6/build/auto.quote.bind.issue.v2.l0.json](../../../../examples/v0.6/build/auto.quote.bind.issue.v2.l0.json)
