#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

node scripts/pipeline-expand.mjs 0.6/pipelines/auto.fnol.fasttrack.v1.l2.yaml 0.6/build/auto.fnol.fasttrack.v1.l0.json
node 0.6/tests/fnol-fasttrack.spec.mjs --l0 0.6/build/auto.fnol.fasttrack.v1.l0.json
