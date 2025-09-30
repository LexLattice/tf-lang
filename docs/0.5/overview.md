# 0.5 Overview

The 0.5 cycle keeps the A→F rails intact while tightening determinism and the hand-off between the CLI, optimizer, proofs, and runtime surfaces. Start here for a map of artifacts, commands, and quickstarts that let you run every track locally without guesswork.

## Pipeline at a glance
```
Compose (.tf) ──▶ Parse / Format ──▶ Canonical IR ──▶ Optimizer ──▶ Proofs ──▶ Runtime ──▶ Trace & Perf
                      │                │                │             │             │             │
                      ▼                ▼                ▼             ▼             ▼             ▼
                DSL spec & fmt   Manifest + law    used_laws &   SMT stubs &   TS/RS codegen   JSONL traces
                                   registry refs      rewrites         coverage        + parity
```

Reference material: DSL + formatter ([`docs/l0-dsl.md`](../l0-dsl.md)), catalogs/effects ([`docs/l0-catalog.md`](../l0-catalog.md), [`docs/l0-effects.md`](../l0-effects.md)), optimizer rewrites ([`docs/proofs/README.md`](../proofs/README.md#manifest-validation-ci-gatemjs---check-used)), and parity harness details ([`docs/pilot-l0.md`](../pilot-l0.md)).

*Determinism:* every emitted JSON/JSONL file is newline-terminated with sorted keys. Trace harnesses replay under fixed clocks—see the [pilot parity harness](../pilot-l0.md#parity-harness) for how we enforce this in CI.

## Tracks

| Track | Goal | Artifacts | Primary CLI |
| --- | --- | --- | --- |
| **A. Parse & Format** | Canonical DSL parsing, formatter, catalog ingest | `out/0.5/ir/*.json`, refreshed catalog/effects | `pnpm run a1`, `pnpm run tf -- parse`, `pnpm run tf -- fmt` |
| **B. Runtime & Composition** | Deterministic IR, manifests, generated runners | `out/0.5/pilot-l0/**`, generated TS runtime | `PILOT_OUT_DIR=out/0.5/pilot-l0 pnpm run pilot:build-run`, `pnpm run tf -- canon`, `pnpm run tf -- emit` |
| **C. Trace & Perf** | Capture/validate traces, summarize perf, parity diffs | `out/0.5/pilot-l0/trace.jsonl`, summaries under `out/0.5/**` | `pnpm run traces:validate`, `pnpm run traces:sample`, `pnpm run pilot:parity` |
| **D. Optimizer** | Effect-aware rewrites + law manifests | `out/0.5/proofs/used-laws.json`, optimized plans | `node packages/tf-opt/bin/opt.mjs --ir … --emit-used-laws …` |
| **E. Proofs** | Emit SMT/Alloy suites and confirm coverage | `out/0.5/proofs/**/*.smt2`, coverage reports | `pnpm run proofs:emit`, `node scripts/proofs/coverage.mjs --out out` |
| **F. Release & DevEx** | Audits, determinism probes, docs + CI health | Audit JSON, determinism logs, link check | `pnpm run audit`, `pnpm run determinism`, `pnpm run docs:check` |

* Jump directly into execution via the per-track quickstarts: [A](quickstarts/track-a-parse-format.md), [B](quickstarts/track-b-runtime.md), [C](quickstarts/track-c-trace-perf.md), [D](quickstarts/track-d-optimizer.md), [E](quickstarts/track-e-proofs.md), [F](quickstarts/track-f-release-devex.md).
* Deep dives: DSL + catalog ([`docs/l0-dsl.md`](../l0-dsl.md), [`docs/l0-catalog.md`](../l0-catalog.md)), optimizer outputs ([`docs/proofs/README.md`](../proofs/README.md#manifest-validation-ci-gatemjs---check-used)), and law registry upkeep ([`docs/proofs/README.md`](../proofs/README.md#law-stubs-scriptsproofslaws)).

## Workspace setup

```bash
pnpm -v && node -v
pnpm -w -r install --frozen-lockfile
pnpm -w -r build
```

After installing, the quickstarts assume you are inside the repo root with `pnpm` on your `PATH`.

## Troubleshooting

> **Frozen installs** – Always prefer `pnpm -w -r install --frozen-lockfile`. If pnpm reports lock drift, run `pnpm -w install --lockfile-only` and retry the install.
>
> **Missing optional deps in fast tests** – Product `fast` runners intentionally skip heavy integrations. Re-run with `pnpm run test:heavy --allow-missing-deps` when you need the full surface.
>
> **Law manifests** – Coverage failures usually mean the optimizer emitted a law with no stub. Revisit [`docs/proofs/README.md`](../proofs/README.md#law-stubs-scriptsproofslaws) to add the stub before re-running `node scripts/proofs/coverage.mjs --out out`.
