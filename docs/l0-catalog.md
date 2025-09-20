# L0 Catalog (A1 skeleton)
- `spec/ids.json` — IDs
- `spec/catalog.json` — normalized catalog with placeholders
- `spec/effects.json` — derived effect tags
- `spec/laws.json` — law registry (sample rules)

### Seed Overlay
Until the legacy YAML catalogs are fully curated, the A1 pipeline unions any
`spec/seed/*.json` overlay into the generated catalog. The seed entries carry
minimal `effects`, `reads`/`writes`, and `qos` data so the checker, flows, and
conflict detection stay runnable while curation continues.
