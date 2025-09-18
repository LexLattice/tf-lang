# Transport Oracle (TS)

Ensures runtime values remain stable across JSON serialization and deserialization.

- **Package:** `@tf/oracles-transport`
- **Input:** `{ value: unknown }`
- **Success:** JSON round-trip preserves the canonicalized runtime value.
- **Failure:** First mismatch reported with JSON Pointer and before/after values.

## Scripts

- `pnpm --filter @tf/oracles-transport build`
- `pnpm --filter @tf/oracles-transport test`
