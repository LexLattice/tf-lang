# Conservation Oracle

**Goal:** Verify that specified quantities are conserved between a **before** and an **after** snapshot.

## Input (example fixture)
```json
{
  "version": "0.1.0",
  "subject": "conservation",
  "keys": ["records", "warnings"],
  "before": { "records": 100, "warnings": 2 },
  "after":  { "records": 100, "warnings": 2 }
}
```

## Output (report.json)
```json
{
  "version": "0.1.0",
  "ok": true,
  "violations": []
}
```

If a key differs, emit:
```json
{ "key": "records", "before": 100, "after": 98, "delta": -2 }
```
All keys sorted; canonical JSON; trailing newline.
