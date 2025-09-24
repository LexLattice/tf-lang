# TF VS Code Client Assets

This extension keeps generated artifacts (the compiled JavaScript bundle, the
packaged VSIX, and extracted language-server bundles) out of source control to
comply with the repository "no binary" policy. Use the helper script to rebuild
and verify them when you need to run the smoke tests or publish the client.

```bash
./regenerate_assets.sh
```

The script recompiles the extension, re-bundles the language server, emits a
deterministic VSIX at `out/0.45/vscode/clients-vscode-tf.vsix`, and rewrites
`CHECKSUMS.sha256` with the expected SHA-256 digests.

To verify the assets after generation:

```bash
(cd ../../out/0.45/vscode && sha256sum --check ../../../clients/vscode-tf/CHECKSUMS.sha256)
```

> The checksum file uses paths relative to `out/0.45/vscode` so the verification
> command must run from that directory.
