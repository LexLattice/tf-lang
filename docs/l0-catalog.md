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

### Effect derivation rules
Deterministic name-based rules fill in missing effect tags and network QoS only when the catalog lacks curated data.
Seed overlays remain authoritative for existing effects or qos values.
Hashing primitives classify as Pure; Crypto is reserved for secret-bearing operations (sign/verify/encrypt/decrypt).

### Manifest compatibility
For the 0.4 release we emit both the legacy manifest fields (`effects`, flat `footprints`) and the new shape (`required_effects`, structured `footprints_rw`, `qos`).
The schema-backed validator accepts either shape so downstream tooling can migrate at its own pace.
Use `node scripts/validate-manifest.mjs <file>` to confirm a manifest satisfies the compatibility contract.
