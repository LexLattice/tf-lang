#!/usr/bin/env bash
set -euo pipefail
pipelines_built=0
monitors_built=0
diagrams_written=0
# Pipelines
node scripts/pipeline-expand.mjs 0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml 0.6/build/auto.fnol.fasttrack.v1.l0.json
((pipelines_built+=1))
node scripts/assert-kernel-only.mjs 0.6/build/auto.fnol.fasttrack.v1.l0.json
node 0.6/tests/fnol-fasttrack.spec.mjs --l0 0.6/build/auto.fnol.fasttrack.v1.l0.json
node scripts/pipeline-expand.mjs 0.6/pipelines/auto.quote.bind.issue.v2.l2.yaml 0.6/build/auto.quote.bind.issue.v2.l0.json
((pipelines_built+=1))
node scripts/assert-kernel-only.mjs 0.6/build/auto.quote.bind.issue.v2.l0.json
node 0.6/tests/quote-bind-issue.spec.mjs --l0 0.6/build/auto.quote.bind.issue.v2.l0.json
# Monitors
node scripts/monitor-expand.mjs 0.6/monitors/fasttrack-24h.l2.yaml 0.6/build/monitors.fasttrack-24h.l0.json
((monitors_built+=1))
node scripts/assert-kernel-only.mjs 0.6/build/monitors.fasttrack-24h.l0.json
node 0.6/tests/monitors-fasttrack-24h.spec.mjs --l0 0.6/build/monitors.fasttrack-24h.l0.json
# Diagrams
node tools/tf-lang-cli/index.mjs graph 0.6/build/auto.fnol.fasttrack.v1.l0.json > diagrams/auto.fnol.fasttrack.v1.dot
((diagrams_written+=1))
node tools/tf-lang-cli/index.mjs graph 0.6/build/auto.quote.bind.issue.v2.l0.json > diagrams/auto.quote.bind.issue.v2.dot
((diagrams_written+=1))
node tools/tf-lang-cli/index.mjs graph 0.6/build/monitors.fasttrack-24h.l0.json > diagrams/monitors.fasttrack-24h.dot
((diagrams_written+=1))
if command -v dot >/dev/null 2>&1; then
  dot -Tsvg diagrams/auto.fnol.fasttrack.v1.dot -o diagrams/auto.fnol.fasttrack.v1.svg
  dot -Tsvg diagrams/auto.quote.bind.issue.v2.dot -o diagrams/auto.quote.bind.issue.v2.svg
  dot -Tsvg diagrams/monitors.fasttrack-24h.dot -o diagrams/monitors.fasttrack-24h.svg
fi
echo "All examples OK."
echo "Summary: ${pipelines_built} pipelines, ${monitors_built} monitor bundles, ${diagrams_written} diagrams."
