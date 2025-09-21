# L0 Tools

## Verify a JSONL trace against IR (+optional manifest/catalog)

```bash
node packages/tf-compose/bin/tf-verify-trace.mjs \
  --ir out/0.4/ir/signing.ir.json \
  --trace tests/fixtures/trace-ok.jsonl \
  --manifest tests/fixtures/manifest-limited.json \
  --catalog packages/tf-l0-spec/spec/catalog.json
# => {"ok":true,"issues":[],"counts":{"records":2,"unknown_prims":0,"denied_writes":0}}
```
