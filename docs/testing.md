# Test harness quick reference

## Authoring `@tf-test` headers

Every automated test must start with a metadata comment. The harness reads only the first comment block in the file and fails with the exact message `Missing @tf-test header in <file>` if the marker is absent.

Either of the following styles is accepted:

```js
// @tf-test kind:product speed:fast deps:none
```

```js
/*
 * @tf-test
 * kind=product
 * speed=fast
 * deps=rust,z3
 */
```

### Supported keys

| Key   | Required | Notes |
| ----- | -------- | ----- |
| `kind` | ✅ | Lane selector such as `product`, `infra`, `parity`, etc. |
| `speed` | ✅ | Choose among tiers like `fast`, `medium`, or `product`. |
| `deps` | ✅ | Comma-separated dependency tags (`node`, `rust`, `z3`, or `none`). |
| `area` | ➖ | Optional; defaults to `misc` when omitted. |

Unknown keys are ignored so you can add additional metadata as needed.

## Running the harness

Select lanes with the speed filter:

```bash
node scripts/test/run.mjs --speed fast
node scripts/test/run.mjs --speed product
```

The `fast` lane implicitly enables `--allow-missing-deps`, treating absent heavy toolchains as skips. Other lanes require declared tooling and still mark missing dependencies as skipped entries, but they keep `ok` false in the manifest so the issue is visible.

Each run produces `out/0.4/tests/manifest.json` with aggregated results:

```jsonc
{
  "ok": true,
  "selected": 5,
  "run": { "node": 5, "vitest": 0, "cargo": 0 },
  "skipped": [
    { "file": "tests/example.test.mjs", "reason": "missing rust" }
  ],
  "durations": {
    "totalMs": 123.456,
    "byRunner": { "node": 123.456, "vitest": 0, "cargo": 0 },
    "byTest": [
      { "file": "tests/example.test.mjs", "runner": "node", "ms": 24.321 }
    ]
  }
}
```

Values are numeric and rounded to three decimals. `ok` is `true` only when every executed test passes and all required dependencies are present.
