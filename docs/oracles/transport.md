# Transport Oracle (serialize/round-trip)

**Goal:** JSON round‑trip is stable and canonical across runtimes.

## Input (example fixture)
```json
{
  "version": "0.1.0",
  "subject": "transport",
  "value": { "a": 1, "b": [2,3] }
}
```

## Output (report.json)
```json
{
  "version": "0.1.0",
  "ok": true,
  "diff": []
}
```
Where `diff` lists pointer paths that changed under round-trip (should be empty).
