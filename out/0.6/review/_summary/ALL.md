# TF-Lang v0.6 · Top issues roll-up

| Issue | Repro | Owner | Target |
| --- | --- | --- | --- |
| Inline comment parsing crashes expander & examples (`tasks/run-examples.sh`) | `bash tasks/run-examples.sh` | Platform (Tracks A/B/D) | 2024-05-31 |
| Law checker ignores attached metadata; CRDT/jsonpatch coverage incomplete | `node tools/tf-lang-cli/index.mjs laws --check examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json` | L1 Macros (Track E) | 2024-06-07 |
| Runtime duplicates transform logic; no `tf run` to execute L0 graphs | `node packages/runtime/run.mjs examples/v0.6/build/auto.fnol.fasttrack.v1.l0.json` | Checker/Runtime (Track C) | 2024-06-07 |
| Release gates undefined for typecheck/effects; manifests stale | `node tools/tf-lang-cli/index.mjs typecheck examples/v0.6/build/auto.quote.bind.issue.v2.l0.json` | Release (Track G) | 2024-06-14 |
| Docs still reference v0.5; onboarding lacks glossary/quickstart | `open README.md` | Docs/DX (Track H) | 2024-05-24 |
