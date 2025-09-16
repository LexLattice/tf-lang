# Idempotence Oracle

**Goal:** Applying an operation **twice** yields the **same** result as once.

## Input (example fixture)
```json
{
  "version": "0.1.0",
  "subject": "idempotence",
  "input": { "data": [1,2,3] }
}
```

The oracle will call the provided function/adapter twice (or simulate via fixture pairs) and compare canonical outputs.

## Output (report.json)
```json
{
  "version": "0.1.0",
  "ok": true,
  "mismatches": []
}
```
Each mismatch lists `path` and the differing canonical values.
