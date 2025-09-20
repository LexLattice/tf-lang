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
For v0.4 manifests we emit both the legacy `effects`/`footprints` shape and the new `required_effects`/`footprints_rw` plus `qos` block so downstream tools stay compatible.
The JSON schema and validator accept either layout, making it safe to mix old and new consumers during the rollout.
