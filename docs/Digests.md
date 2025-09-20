# Deterministic Digests

Write a manifest of all `out/0.4/**` file hashes:

```bash
npm run digest:out
```

Outputs:
- `out/0.4/digests.txt` — sorted `sha256:...  path` lines
- `out/0.4/digests.json` — `{ files: [{path, sha256}], manifest_sha256 }`

The `manifest_sha256` is the hash of the `digests.txt` content and serves as a single-line attestation for the entire build.
