# Track D · Examples & Monitors

## What exists now
- **Canonical examples** under `examples/v0.6/`: two pipelines (`auto.fnol.fasttrack.v1`, `auto.quote.bind.issue.v2`), one monitor bundle (`fasttrack-24h`).
- **Prebuilt artifacts** in `examples/v0.6/build/*.l0.json` enable downstream tooling without re-expansion.
- **Spec harness** (`examples/v0.6/tests/*.spec.mjs`): asserts kernel-only nodes, RPC corr/reply pairing, metric tag hygiene, monitor effects (Inbound/Outbound presence).
- **Docs**: `docs/0.6/pipelines/*.md` and `docs/0.6/monitors/fasttrack-24h.md` embed DOT snapshots for visual review.

## How to run
```bash
# Run quote→bind example checks against shipped L0
node examples/v0.6/tests/quote-bind-issue.spec.mjs --l0 examples/v0.6/build/auto.quote.bind.issue.v2.l0.json

# Monitor bundle smoke (effects + RPC pairing)
node examples/v0.6/tests/monitors-fasttrack-24h.spec.mjs --l0 examples/v0.6/build/monitors.fasttrack-24h.l0.json

# (Intended) end-to-end regen + diagrams
bash tasks/run-examples.sh   # currently fails on inline comments
```

## Common errors + fixes
- Spec scripts exit with `Missing --l0 <path>` if flag omitted; always pass explicit path even when running from build dir.
- Regenerating from L2 hits the same inline `# types:` comment parsing bug; strip trailing comments before running the scripts.
- DOT → SVG conversion requires Graphviz (`dot`). Without it, the script silently skips SVG emission; advise `apt-get install graphviz` for doc reviewers.

## Gaps
- No README tying the three example commands together or mapping artifacts → docs.
- `tasks/run-examples.sh` fails immediately, so CI-friendly smoke is unavailable.
- Monitor spec docs lack explanation of effect expectations (why Outbound/Inbounds appear) beyond the DOT.

## Next 3 improvements
1. Fix L2 parsing so `tasks/run-examples.sh` is a one-command success story (build → test → diagrams) for onboarding.
2. Add `examples/v0.6/README.md` summarizing pipeline purpose, expansion command, checker invocation, and monitor expectations.
3. Emit example-specific capability manifests + checker reports into `out/0.6/examples/` and link them from docs for audit trails.
