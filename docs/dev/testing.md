# Test harness quick reference

## Authoring `@tf-test` headers

Every runnable test must start with an `@tf-test` metadata block; the harness exits with `Missing @tf-test header (add: "@tf-test kind:<...> speed:<...> deps:<...>")` when the marker is absent. Use either the single-line or block-style comment:

```js
// @tf-test kind=product speed=fast deps=node
```

```js
/*
 * @tf-test
 * kind=product
 * speed=fast
 * deps=node
 */
```

The harness requires three keys:

- `kind` – the lane identifier (`infra`, `product`, `parity`, etc.).
- `speed` – `fast`, `medium`, or `product` are the common tiers.
- `deps` – comma-separated dependency tags. Use `deps=none` when the test has no external requirements.

Additional fields such as `area` are optional; unknown keys are ignored.

### Recognized dependency tags

| Tag  | Meaning                                      |
| ---- | -------------------------------------------- |
| node | Node.js (always available in CI)             |
| rust | The Rust toolchain (`cargo`, `rustc`, etc.)   |
| z3   | The Z3 SMT solver                             |

The harness also accepts `none` in the `deps` list to indicate no special tooling.

## Running fast and product lanes locally

Select tests by metadata using the harness:

```bash
node scripts/test/run.mjs --speed fast
node scripts/test/run.mjs --speed product
```

When `--speed fast` is requested the harness automatically enables `--allow-missing-deps`, recording absent heavy toolchains (for example Rust or Z3) as skips instead of hard failures. Other lanes treat missing declared dependencies as failures and exit with status `1`.

Each invocation writes a manifest to `out/0.4/tests/manifest.json` describing the run:

```jsonc
{
  "ok": true,
  "selected": 42,
  "run": { "node": 40, "vitest": 2, "cargo": 0 },
  "skipped": [
    { "file": "tests/example.test.mjs", "reason": "missing rust" }
  ],
  "durations": {
    "totalMs": 1234.567,
    "byRunner": { "node": 1100.123, "vitest": 134.444, "cargo": 0 },
    "byTest": [
      { "file": "tests/example.test.mjs", "runner": "node", "durationMs": 27.5, "ok": true }
    ]
  }
}
```

`ok` remains `true` only when every executed test passes and all required dependencies are available.
