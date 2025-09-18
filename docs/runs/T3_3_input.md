# T3_3 — Synthesis Input

| Label | PR | Link | State |
|--:|--:|:--|:-----|

### Diff Similarity Summary

- Per-PR changed lines: A:811,B:510,C:696
- Common across all: 121/1654 (7.3%)
- Pairwise Jaccard similarity (intersection/union):
  - A ↔ B: 14.0% (162/1159)
  - A ↔ C: 13.0% (173/1334)
  - B ↔ C: 14.1% (149/1057)
| A | #123 | https://github.com/LexLattice/tf-lang/pull/123 | OPEN |

---

## Run A — PR #123 — Add idempotence oracle and harness reports

### PR Body

## Summary
- add a TypeScript idempotence oracle with JSON-pointer diffs and canonical comparisons
- add focused fixtures, property tests, and seeds for the new oracle
- introduce a minimal harness that runs the idempotence oracle (N=1) and emits canonical reports & certificate artifacts

## Evidence
- [x] `out/t3/idempotence/report.json`
- [x] `out/t3/oracles-report.json`
- [x] `out/t3/certificate.json`
- [x] `out/t3/harness-seeds.jsonl`
- [ ] `out/t3/conservation/report.json`
- [ ] `out/t3/transport/report.json`

## Determinism & Seeds
- Harness seeds: `0x00000001`
- Oracle context `now`: `0`

## Tests & CI
- `pnpm --reporter=append-only -C packages/oracles/idempotence test`
- `pnpm --reporter=append-only -C packages/oracles/harness run build-reports`

## Implementation Notes
- Harness currently exercises only the idempotence oracle (S2 conservation pending)
- Reports are newline-terminated canonical JSON with accompanying SHA-256 files

## Hurdles/Follow-ups
- Implement conservation oracle + report (S2)
- Expand harness coverage to conservation/transport and add parity checks

------
https://chatgpt.com/codex/tasks/task_e_68cc3931275883209233b54d5fe15f6a

### AI Comments (issue)


### AI Reviews

- **@gemini-code-assist** [COMMENTED]: ## Code Review

This pull request introduces idempotence and conservation oracles, along with a test harness and reporting. The implementation is well-structured and includes thorough tests. My review focuses on improving code clarity, maintainability, and adherence to standards. Key suggestions include refactoring duplicated logic in the test harness, simplifying build scripts, and correcting a deviation from the JSON Pointer RFC. I've also pointed out several opportunities for minor code simplifications and using imported types in tests for better maintainability.

### AI Review Comments (inline)

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/index.ts#:173): 

![high](https://www.gstatic.com/codereviewagent/high-priority.svg)

According to RFC 6901 for JSON Pointers, an empty string (`""`) is used to refer to the entire document. This implementation returns `/` for an empty path, which is a deviation from the standard. While this might be a consistent convention within this project, adhering to the standard would be better for interoperability.

```typescript
  if (segments.length === 0) {
    return "";
  }
```

- **@gemini-code-assist[bot]** (packages/oracles/conservation/src/index.ts#:84): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The type of `declared` is `ReadonlyArray<string> | undefined`, so `key` is always a string within this loop. The `typeof key === "string"` check is redundant and can be removed for conciseness.

```suggestion
      if (key) {
        result.add(key);
      }
```

- **@gemini-code-assist[bot]** (packages/oracles/conservation/tests/oracle.spec.ts#:58): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The type assertion for `details` is quite long and duplicates the structure of `ConservationViolation`. You can import `ConservationViolation` from `../src/index.js` and use it in the assertion to make the code cleaner and more maintainable.

```suggestion
      const details = result.error.details as { violations?: ReadonlyArray<ConservationViolation> } | undefined;
```

- **@gemini-code-assist[bot]** (packages/oracles/harness/package.json#:12): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The `build-reports` script can be made more concise by using `pnpm`'s ability to filter multiple packages in a single command. This improves readability and makes it easier to add or remove packages from the build step.

```suggestion
    "build-reports": "pnpm --reporter=append-only -r --filter \"{@tf/oracles-core,@tf/oracles-idempotence,@tf/oracles-conservation,@tf-lang/utils}\" build && pnpm build && node dist/index.js"
```

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/index.ts#:95): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The logic for running the idempotence and conservation oracles within this loop is very similar and largely duplicated. This could be refactored into a generic `runOracle` function to improve maintainability and reduce code duplication. You could define an array of oracle configurations and loop through them inside the `seed` loop.

For example, you could create a helper function like this:
```typescript
async function runOracle(
  oracleConfig: {
    name: string;
    check: (input: any, ctx: OracleCtx) => Promise<OracleResult<any>>;
    buildInput: (seed: string) => any;
    extractFailure: (details: unknown) => OracleReport["firstFail"] | undefined;
  },
  report: OracleReport,
  seed: string,
  ctx: OracleCtx,
): Promise<{ runtime: number; log: string }> {
  // ... implementation ...
}
```

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/index.ts#:66): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

Converting the runtime to a fixed-precision string and then back to a number is a bit convoluted. A more direct approach for rounding to a specific number of decimal places would be to use mathematical operations, which avoids the overhead of string conversions.

```suggestion
        runtime: Math.round(idempotenceRuntime * 1e6) / 1e6,
```

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/index.ts#:92): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

Similar to the idempotence runtime calculation, this can be simplified to avoid converting to a string and back to a number just for rounding.

```suggestion
        runtime: Math.round(conservationRuntime * 1e6) / 1e6,
```

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/index.ts#:121): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The `.map()` call here is redundant. The `recordArtifacts` function already returns an array of objects containing only the `path` and `sha256` properties. You can directly assign `artifacts` to the `artifacts` property of the certificate object.

```suggestion
    artifacts,
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/index.ts#:127): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The use of intermediate variables `missingLeft` and `missingRight` makes this block more verbose than necessary. You can directly construct the return object for better conciseness.

```typescript
      const pointer = pointerFromSegments([...segments, max]);
      return {
        pointer,
        left: left.length > right.length ? left[max] ?? null : MISSING_VALUE,
        right: right.length > left.length ? right[max] ?? null : MISSING_VALUE,
      };
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/tests/oracle.spec.ts#:66): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

Instead of partially defining the type for `mismatches` inline, you can import and use the `IdempotenceMismatch` type from `../src/index.js`. This makes the test more robust to changes in the `IdempotenceMismatch` type and improves readability.

```suggestion
      const details = result.error.details as { mismatches?: ReadonlyArray<IdempotenceMismatch> } | undefined;
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/tests/oracle.spec.ts#:113): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

Similar to another comment, you can use the imported `IdempotenceMismatch` type here instead of redefining its structure inline. This improves maintainability and ensures type safety.

```suggestion
    const details = result.error.details as { mismatches?: ReadonlyArray<IdempotenceMismatch> } | undefined;
```

- **@chatgpt-codex-connector[bot]** (packages/oracles/harness/src/index.ts#:66): 

**[P1] Remove real-time timestamps from harness reports**

`main` writes `now: new Date().toISOString()` when logging seeds and again when emitting `generatedAt` in the certificate, so each execution emits different JSON and SHA256s even if inputs and seeds are fixed. The repo instructions call for deterministic artifacts; these wall-clock timestamps make `harness-seeds.jsonl` and `certificate.json` non-reproducible. Consider deriving timestamps from the fixed oracle context (`CONTEXT_NOW`) or otherwise freezing them so reruns stay byte-for-byte identical.

Useful? React with 👍 / 👎.

| B | #124 | https://github.com/LexLattice/tf-lang/pull/124 | OPEN |

---

## Run B — PR #124 — feat: add TS idempotence oracle harness and reports

### PR Body

## Summary
- implement the TypeScript idempotence oracle with JSON-pointer mismatch reporting and canonicalized comparisons
- add fixtures, tests, and build configuration for the new oracle package
- introduce a minimal harness that emits the idempotence report, seed log, roll-up, and certificate under `out/t3/`

## Evidence (artifacts)
- ✅ `out/t3/idempotence/report.json`
- ✅ `out/t3/oracles-report.json`
- ✅ `out/t3/certificate.json`
- ✅ `out/t3/harness-seeds.jsonl`
- ❌ `out/t3/conservation/report.json`
- ❌ `out/t3/transport/report.json`
- ❌ `out/t3/parity/idempotence.json`
- ❌ `out/t3/parity/conservation.json`
- ❌ `out/t3/parity/transport.json`

## Determinism & Seeds
- Seeds: `0xidempotence0001`
- Harness repeats per seed: 1
- Harness evidence: `out/t3/harness-seeds.jsonl`

## Tests & CI
- `pnpm --reporter=append-only -C packages/oracles/idempotence test`
- `pnpm --reporter=append-only -C packages/oracles/harness run build-reports`
- `pnpm --reporter=append-only -C packages/oracles/idempotence build`
- `pnpm --reporter=append-only -C packages/utils build`
- `pnpm --reporter=append-only -C packages/oracles/core build`

## Implementation Notes
- the idempotence oracle reuses the shared canonicalizer, computes decorated JSON-pointer mismatches, and returns detailed failure traces
- the harness reuses repo-root discovery, generates deterministic cases from the seed, and writes canonical JSON plus SHA-256 sums for artifacts

## Hurdles / Follow-ups
- Conservation, transport, and parity oracles remain to be implemented in subsequent sprints


------
https://chatgpt.com/codex/tasks/task_e_68cc3931275883209233b54d5fe15f6a

### AI Comments (issue)


### AI Reviews

- **@gemini-code-assist** [COMMENTED]: ## Code Review

This pull request introduces an idempotence oracle and a test harness, which is a great addition for ensuring the stability of operations. The implementation is solid, with good test coverage and clear separation of concerns. I've found a few areas for improvement, mainly related to code duplication, a potential logic issue in error reporting, and some minor code style suggestions. My comments include suggestions to address these points to enhance maintainability and correctness.

### AI Review Comments (inline)

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/build-reports.ts#:118): 

![high](https://www.gstatic.com/codereviewagent/high-priority.svg)

In this fallback logic, the number of failed cases is set to `1` if there are any cases. This can be misleading if there are multiple test cases. If a detailed report is unavailable, it's safer to consider all cases as failed to avoid incorrect reporting of passed tests.

```suggestion
  const failed = total;
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/index.ts#:94): 

![high](https://www.gstatic.com/codereviewagent/high-priority.svg)

The `escapeSegment` function is a duplicate of the one in `packages/oracles/idempotence/src/diff.ts`. To avoid code duplication, please remove this implementation and import the function from `diff.ts` instead (after exporting it as suggested in my other comment). This will improve maintainability.

- **@gemini-code-assist[bot]** (.gitignore#:87): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

This block of rules appears to be redundant. The changes from lines 35-39 cover the same patterns. To keep the `.gitignore` file clean and maintainable, this duplicated block should be removed.

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/build-reports.ts#:181): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The SHA256 hash of the certificate file is calculated by reading the file back from disk after writing it. This is unnecessary as the content is already available in memory. You can improve efficiency by hashing the canonicalized string content before writing it to the file, avoiding an extra file read operation.

```suggestion
  const certificateContent = canonicalJson(certificate);
  await writeFile(certificatePath, certificateContent, "utf8");
  const hash = createHash("sha256").update(certificateContent).digest("hex");
  await writeFile(`${certificatePath}.sha256`, `${hash}\n`, "utf8");
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/diff.ts#:66): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The `.values()` call on the `Set` is redundant here. `Array.from()` can directly convert a `Set` to an array. Removing it makes the code slightly cleaner and more concise.

```suggestion
  const orderedKeys = Array.from(keys).sort();
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/diff.ts#:90): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

This helper function is also used in `index.ts`, creating code duplication. Please export it so it can be imported and reused.

```suggestion
export function escapeSegment(segment: string): string {
```

- **@chatgpt-codex-connector[bot]** (packages/oracles/harness/src/build-reports.ts#:53): 

**[P1] Avoid overwriting idempotence report for multiple seeds**

The harness loops over every seed but writes each run to the fixed file `out/t3/idempotence/report.json` and pushes a `NamedReport` with the same `name` for every iteration. If the seeds list is expanded (e.g. to satisfy the deterministic “repeat twice” requirement or to cover future scenarios), each pass will overwrite the previous report on disk while the roll‑up and certificate will still count every entry. This means only the last seed’s results are preserved and the totals reported in `oracles-report.json` can no longer be reproduced from the artifacts on disk. Consider writing unique per-seed paths or aggregating into a single report before writing once so that multiple seeds are handled correctly.

Useful? React with 👍 / 👎.

| C | #125 | https://github.com/LexLattice/tf-lang/pull/125 | OPEN |

---

## Run C — PR #125 — Add TypeScript idempotence oracle harness and utilities

### PR Body

## Summary
* add the shared `@tf/oracles-core` helpers for canonicalization, oracle contexts, and normalized success/failure envelopes. 
* ship the TypeScript idempotence oracle package with fixtures, seeds, and richer property/fixture coverage for nested and null edge cases. 
* wire up an initial harness package that runs the idempotence fixtures, exports reusable helpers, and emits deterministic report + certificate artifacts.

## Evidence
- [x] out/t3/idempotence/report.json
- [x] out/t3/oracles-report.json
- [x] out/t3/oracles-report.json.sha256
- [x] out/t3/certificate.json
- [x] out/t3/harness-seeds.jsonl
- [x] out/t3/_status.json
- [x] out/t3/_progress.log
- [x] out/t3/_pause_summary.json

## Determinism & Seeds
* Seeds: 0x5eed-idem-0001 (fixtures harness)
* Repeats: 1 per fixture (downshifted per brief)
* Fixtures: packages/oracles/idempotence/fixtures/{happy,mismatch}.json

## Tests & CI
* ✅ `pnpm --reporter=append-only -C packages/oracles/core test`
* ✅ `pnpm --reporter=append-only -C packages/oracles/idempotence test`
* ✅ `pnpm --reporter=append-only -C packages/oracles/harness test`
* ✅ `pnpm -C packages/oracles/harness run build-reports`

## Implementation Notes
* Harness exports (`runIdempotence`, `writeJson`, `writeSha256`, `readSha`, `relativePath`) are reused in Vitest for deterministic newline/SHA coverage.
* Property-based tests extend the oracle coverage to nested pointers and null-vs-missing divergences while keeping seeds fixed via `tests/seeds.json`.
* Shared canonical helpers drop `undefined`, normalize `Set`, `Date`, non-finite numbers, and trace/warning dedupe for consistent JSON pointers.
* Produced `_pause_summary.json` manually because the stock analyzer script targets T1 paths.

## Hurdles/Follow-ups
* Next sprints: implement conservation/transport oracles plus parity harness (per roadmap).
* Consider generalizing pause-analysis tooling to T3 paths for future runs.


------
https://chatgpt.com/codex/tasks/task_e_68cc3931275883209233b54d5fe15f6a

### AI Comments (issue)


### AI Reviews

- **@gemini-code-assist** [COMMENTED]: ## Code Review

This pull request introduces a suite of packages for running idempotence oracles, including a core library for canonicalization and results, an idempotence oracle implementation, and a test harness for generating reports. The changes are well-structured and include thorough testing with property-based tests and fixtures. My review focuses on improving robustness, maintainability, and adherence to standards. Key suggestions include making type assertions safer, improving the JSON pointer implementation to follow RFC 6901, and cleaning up some duplicate type definitions.

### AI Review Comments (inline)

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/tests/oracle.spec.ts#:166): 

![high](https://www.gstatic.com/codereviewagent/high-priority.svg)

You've redefined the `IdempotenceMismatch` interface locally. This is risky because it can diverge from the actual type definition in `src/types.ts`, leading to tests that pass incorrectly or are hard to understand. Please remove this local definition and import the original type from `../src/types.js`. You will also need to update the type casts in your tests to use the imported type. Note that `IdempotenceMismatch` may need to be exported from the main package entry point first.

- **@gemini-code-assist[bot]** (packages/oracles/core/src/canonical.js#:61): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The creation of the `result` object can be made more concise and readable by using `Object.fromEntries()`. This avoids the manual loop and is a more modern approach to convert an array of key-value pairs into an object. This change also removes the need for the intermediate `input` variable.

```suggestion
        const entries = Object.entries(value)
            .filter(([, entryValue]) => entryValue !== undefined)
            .map(([key, entryValue]) => [key, canonicalizeValue(entryValue)])
            .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
        return Object.fromEntries(entries);
```

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/build-reports.ts#:91): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The type assertion `as { readonly input: IdempotenceInput; }` is not type-safe. If a fixture file has an invalid structure (e.g., the `input` key is missing), `payload.input` will be `undefined`, causing a runtime error on the next line when `checkIdempotence` is called. For better robustness, consider using a type guard or a schema validation library (like Zod) to safely parse and validate the fixture data.

- **@gemini-code-assist[bot]** (packages/oracles/harness/src/build-reports.ts#:100): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

This inline type assertion is brittle and hard to maintain as it duplicates the structure of `IdempotenceMismatch`. If the original type in `@tf/oracles-idempotence` changes, this will not be updated automatically and could lead to subtle bugs. It would be safer to import the `IdempotenceMismatch` type and use it here. This may require exporting `IdempotenceMismatch` from the `@tf/oracles-idempotence` package first.

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/index.ts#:7): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The `IdempotenceMismatch` type is defined and exported in `types.ts` but not re-exported from the package's entry point. This prevents consumers of the package, like the harness and tests, from using this type for safe type assertions. Please export it to improve the package's public API.

```suggestion
export type { IdempotenceCase, IdempotenceInput, IdempotenceMismatch, IdempotenceReport } from "./types.js";
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/index.ts#:129): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

The current `isPlainObject` check is not fully robust, as it will return `true` for instances of classes. A more reliable way to check for a plain object is to inspect its prototype. This ensures that only objects created by `{}` or `new Object()` or `Object.create(null)` are considered plain objects.

```typescript
function isPlainObject(value: unknown): value is Record<string, unknown> {
  if (typeof value !== "object" || value === null || Array.isArray(value)) {
    return false;
  }
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/index.ts#:137): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

Your implementation of JSON Pointers uses `/` to represent the root of the document. This deviates from the RFC 6901 standard, which specifies an empty string `""` for the root. Adhering to the standard would improve interoperability and clarity. According to the RFC, a pointer of `/` refers to a key named `""`.

```typescript
function pointerFromSegments(segments: ReadonlyArray<string | number>): string {
  if (segments.length === 0) {
    return "";
  }
  const encoded = segments.map((segment) => encodePointerSegment(String(segment)));
  return `/${encoded.join("/")}`;
}
```

- **@gemini-code-assist[bot]** (packages/oracles/idempotence/src/index.ts#:149): 

![medium](https://www.gstatic.com/codereviewagent/medium-priority.svg)

To align with the proposed change to use an empty string `""` for the root JSON pointer (per RFC 6901), this function should be updated to no longer treat `/` as the root. The pointer `/` should be correctly parsed as a pointer to a key named `""`, which this change will accomplish.

```typescript
function segmentsFromPointer(pointer: string): ReadonlyArray<string | number> {
  if (pointer === "") {
    return [];
  }
  const segments = pointer.split("/").slice(1);
  return segments.map((segment) => segment.replace(/~1/g, "/").replace(/~0/g, "~"));
}
```

- **@chatgpt-codex-connector[bot]** (packages/oracles/harness/src/build-reports.ts#:83): 

**[P1] Record actual seed used for idempotence runs**

The harness writes `harness-seeds.jsonl` with a fixed seed of `0x5eed-idem-0001`, but `runIdempotence` still instantiates the oracle context with `createOracleCtx("0xfeed", { now: 0 })`. This means the report and certificate claim a different seed than the one used to execute the fixtures, so downstream consumers cannot reproduce the run using the published seed. Consider threading the declared seed into `runIdempotence` (and into the oracle context) so the logged metadata matches the execution.

Useful? React with 👍 / 👎.

