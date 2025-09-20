# PR Notes — Determinism Add-on v3 (with Autofix)

Includes:
- IDs/catalog schema validation (Ajv)
- Determinism gates (ids-only + full-run)
- Trace redaction + deterministic RNG/clock in TS generator
- Linter (schema + rules for footprints/QoS/etc.)
- Digest manifest writer
- **Autofix** (suggest/apply) for missing footprints, QoS, data_classes, and effects

## Autofix usage
- Suggest (no file modifications):
  ```bash
  node scripts/autofix-catalog.mjs --mode suggest
  # outputs: out/0.4/lint/autofix-report.json, autofix.patch.json, catalog.autofixed.json
  ```
- Apply in place:
  ```bash
  node scripts/autofix-catalog.mjs --apply
  ```
- Optional flags:
  - `--config path/to/autofix.config.json` to override defaults
  - `--fail-on-suggestions` to cause CI failure if changes are suggested (useful once the catalog is stable)

Defaults:
- `Network.*` → `qos.delivery_guarantee = "at-least-once"`; `ordering = "per-key"` if `keys[]` present else `"none"`
- `Storage.Read/Write` → add placeholder footprints with `mode` set; `uri = res://TODO/<domain>/<name>`
- Crypto/secret ops → `data_classes = ["secrets"]` if missing
- Empty `effects` → filled using name heuristics (same as derive-effects initial pass)
