# Review: C-Trace-Perf (v0.5)

This document reviews the developer experience and documentation for the Track C (Trace-Perf) toolchain.

## 1. What Exists Now

The `C-Trace-Perf` track is implemented in the `@tf-lang/tf-trace` package. It provides a command-line tool, `tf-trace`, for validating, analyzing, and exporting performance trace data against performance budgets.

- **Trace Schema:** A simple JSONL format for recording timestamped events with associated effects (e.g., `cpu`, `io`) and durations.
- **Budget Schema:** A JSON format for defining performance limits, including a total time budget (`total_ms_max`) and per-effect constraints on time (`ms_max`) and event count (`count_max`).
- **CLI Tool (`tf-trace`):** A single executable with four main commands:
    - `validate`: Checks a trace file for schema compliance.
    - `summary`: Aggregates a trace file into a summary of costs per effect.
    - `budget`: Checks a trace summary against a budget file.
    - `export`: Converts a trace summary into a CSV file for external analysis.

## 2. How to Run: 10-Minute Quickstart

This recipe shows how to run a full analysis cycle using the provided sample data.

**Prerequisite:** The tool must be compiled from source first.

```bash
# 1. Compile the tool (one-time setup)
pnpm -C packages/tf-trace build

# 2. Validate the raw trace data (trace_small.jsonl)
node packages/tf-trace/bin/trace.mjs validate --in samples/c/trace_small.jsonl

# Expected Output:
# {"ok":true,"count":6,"errors_count":0}
# validated 6 record(s)

# 3. Create a performance summary
node packages/tf-trace/bin/trace.mjs summary \\
  --in samples/c/trace_small.jsonl \\
  --out out/0.5/review/C-Trace-Perf/summary.json

# Expected Output:
# {"ok":true,"out":"out/0.5/review/C-Trace-Perf/summary.json",...}
# wrote summary to out/0.5/review/C-Trace-Perf/summary.json

# 4. Check the summary against a budget
node packages/tf-trace/bin/trace.mjs budget \\
  --summary-in out/0.5/review/C-Trace-Perf/summary.json \\
  --budgets samples/c/budgets.sample.json

# Expected Output:
# {"ok":true,"reasons":[],...}
# budget check passed

# 5. Export the summary to CSV for triage
node packages/tf-trace/bin/trace.mjs export \\
  --summary out/0.5/review/C-Trace-Perf/summary.json \\
  --csv out/0.5/review/C-Trace-Perf/export.csv

# Expected Output:
# {"ok":true,"csv":"out/0.5/review/C-Trace-Perf/export.csv",...}
# wrote summary csv to out/0.5/review/C-Trace-Perf/export.csv
```

## 3. FAQ & Usability Notes

**Q: What do performance budgets represent?**

- `total_ms_max`: The maximum allowed time for the entire operation. If the sum of all `ms` values in the trace exceeds this, the budget fails.
- `by_effect`: Defines limits for specific categories of work. For example, you can set a maximum `ms_max` for `cpu` time or a `count_max` for `io` operations to detect inefficient patterns.

**Q: What does a red budget mean in CI?**

A "red" or failed budget check (triggered by the `--fail-on-violation` flag) returns a non-zero exit code. In CI, this will fail the build, preventing a performance regression from being merged. This is the primary mechanism for enforcing performance standards.

**Q: How can I share findings with product stakeholders?**

The `export` command generates a CSV file, which can be easily opened in spreadsheet software like Excel or Google Sheets. This allows for simple sorting, filtering, and sharing of performance data with non-technical team members for triage and planning.

## 4. Common Errors + Fixes

- **ERROR:** `Error [ERR_MODULE_NOT_FOUND]: Cannot find module ... dist/lib/ingest.js`
  - **Reason:** The `tf-trace` tool was not compiled from its TypeScript source. The `dist/` directory is missing or stale.
  - **Fix:** Run the build command from the workspace root: `pnpm -C packages/tf-trace build`.

- **ERROR:** `budget check failed` (with a non-zero exit code)
  - **Reason:** The trace summary violated one or more rules in the budget file. The JSON output will contain a `reasons` array explaining which limits were exceeded.
  - **Fix:**
    1.  Analyze the `reasons` output to identify the failing effect or total time.
    2.  Inspect the CSV export or trace summary to understand the source of the high cost.
    3.  Optimize the code path that generated the trace, or if the regression is expected, update the budget file to reflect the new baseline.

## 5. Gaps & DX Friction

1.  **Build Step Required:** The biggest DX hazard is that the tool doesn't work "out of the box" after `pnpm install`. A new developer will hit the `ERR_MODULE_NOT_FOUND` error and must discover the build command in the README. The `postinstall` script for the package should handle this automatically.
2.  **CLI Entrypoint:** The `pnpm install` warnings (`Failed to create bin`) and the need to call the tool via its full `node packages/tf-trace/bin/trace.mjs` path are clumsy. Fixing the `bin` entry in `package.json` would allow for a cleaner `pnpm tf-trace` invocation.
3.  **Silent Failures:** Without `--fail-on-violation`, the `budget` command exits with code 0 even if the budget fails. This is a reasonable default, but the flag should be prominently documented as essential for CI usage.
4.  **Lack of In-Tool Documentation:** The `--help` message is good, but there's no `man` page or detailed explanation of the budget schema or trace format accessible from the CLI itself.

## 6. Next 3 Improvements

1.  **(S) Fix the Build:** Add a `postinstall` script to `packages/tf-trace/package.json` that runs the `build` command automatically. This ensures the tool is ready immediately after installation.
2.  **(S) Fix the CLI `bin`:** Correct the `package.json` `bin` entry and workspace configuration so that `pnpm tf-trace` is a valid command.
3.  **(M) Improve Onboarding Docs:** Enhance the `README.md` to be a full quickstart guide. Move the "How to Run" section from this review into the main README to make it the first thing a new user sees. Explain the `--fail-on-violation` flag's importance for CI.