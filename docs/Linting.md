# Catalog Linter

Run:
```bash
npm run lint:catalog
```

What it checks:
- Schema validity (`schemas/catalog.schema.json`)
- Unique IDs, domain/id consistency
- **Storage.Read** ⇒ non-empty `reads[]` with `uri`
- **Storage.Write** ⇒ non-empty `writes[]` with `uri`
- **Network.*** ⇒ `qos.delivery_guarantee` present
- Warns for `data_classes` likely needed by crypto/secret ops
- Warns if `Pure` declares footprints

Outputs:
- `out/0.4/lint/report.json`
- `out/0.4/lint/summary.txt`

Fails the build on any **errors**; warnings do not fail.
