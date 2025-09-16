# Trace→Tags Schema

## Input (trace)
A JSONL of events:
```json
{"ts":0,"kind":"oracle:start","name":"determinism","seed":"0x1234"}
{"ts":1,"kind":"oracle:ok","name":"determinism","value":{"..."}}
```

## Output (tags)
`out/t2/trace-tags.json`:
```json
{
  "version": "0.1.0",
  "source": "trace2tags",
  "tags": [
    {"task":"T1_3","tag":"determinism.ok","count":42},
    {"task":"T1_4","tag":"conservation.violation","count":3}
  ]
}
```
Rules for mapping live in `packages/mapper/trace2tags/README.md` (emit one row per tag with task id, tag, count). Deterministic order.
