# Idempotence Oracle (TypeScript)

The idempotence oracle ensures that applying a transformation multiple times yields the same result as applying it once. Inputs provide sequences of canonical application outputs; the oracle compares the first output against every subsequent output using canonical JSON equality and reports the first mismatch.

## Scripts

- `pnpm build`
- `pnpm test`
