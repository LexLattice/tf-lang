# Catalog Autofix

Run in **suggest** mode (default):
```bash
node scripts/autofix-catalog.mjs --mode suggest
# See out/0.4/lint/autofix-report.json and catalog.autofixed.json
```

Apply changes in place:
```bash
node scripts/autofix-catalog.mjs --apply
```

Flags:
- `--config <path>`: override defaults (JSON)
- `--fail-on-suggestions`: in suggest mode, exit 2 if any changes are proposed

Heuristics (conservative):
- **Effects**: if empty, fill from name using the same regex rules as the derive step.
- **Storage.Read/Write**: ensure footprints exist; set `mode` (`read`/`write`); add placeholder `uri` when missing.
- **Network.In/Out**: ensure `qos.delivery_guarantee` (default `at-least-once`); set `ordering` to `per-key` if `keys[]` exists, else `none`. Optional `visibility_timeout_ms` can be configured.
- **Crypto/secret** ops: if `data_classes` missing, set to `["secrets"]`.

Outputs:
- `out/0.4/lint/autofix-report.json` — list of patches with reasons
- `out/0.4/lint/autofix.patch.json` — patch array
- `out/0.4/lint/catalog.autofixed.json` — modified catalog copy
