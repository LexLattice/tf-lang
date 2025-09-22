// @tf-test kind=parity area=runtime speed=heavy deps=node

import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { strict as assert } from 'node:assert';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const L0_OUT = path.join(ROOT, 'out', '0.4', 'pilot-full');
const T5_OUT = path.join(ROOT, 'out', 't5-full');
const PARITY_DIR = path.join(ROOT, 'out', '0.4', 'parity', 'full');
const REPORT_PATH = path.join(PARITY_DIR, 'report.json');

function withEnv() {
  return { ...process.env, TF_PILOT_FULL: '1' };
}

function runNode(script) {
  return spawnSync('node', [script], {
    cwd: ROOT,
    stdio: 'inherit',
    env: withEnv(),
  });
}

const SKIP = process.env.TF_PILOT_FULL !== '1';

test('pilot full parity against T5 pipeline', { skip: SKIP }, () => {
  rmSync(L0_OUT, { recursive: true, force: true });
  rmSync(T5_OUT, { recursive: true, force: true });
  rmSync(PARITY_DIR, { recursive: true, force: true });

  const t5 = runNode('scripts/t5-build-run.mjs');
  assert.equal(t5.status, 0, 't5-build-run should succeed');

  const l0 = runNode('scripts/pilot-full-build-run.mjs');
  assert.equal(l0.status, 0, 'pilot-full-build-run should succeed');

  const parity = runNode('scripts/pilot-full-parity.mjs');
  assert.equal(parity.status, 0, 'pilot-full-parity should succeed');

  const reportRaw = readFileSync(REPORT_PATH, 'utf8');
  const report = JSON.parse(reportRaw);
  assert.equal(report.equal, true, 'report should mark equality');
  assert.deepEqual(report.diff, [], 'diff should be empty');

  const parityRepeat = runNode('scripts/pilot-full-parity.mjs');
  assert.equal(parityRepeat.status, 0, 'parity rerun should succeed');
  const reportRepeat = readFileSync(REPORT_PATH, 'utf8');
  assert.equal(reportRepeat, reportRaw, 'report should be stable across runs');

  const ordersPath = path.join(T5_OUT, 'orders.ndjson');
  const originalOrders = readFileSync(ordersPath, 'utf8');
  try {
    const tampered = originalOrders + '\n{"tamper":true}\n';
    writeFileSync(ordersPath, tampered);
    const mismatch = runNode('scripts/pilot-full-parity.mjs');
    assert.equal(mismatch.status, 1, 'parity should fail on mismatch');
    const mismatchReport = JSON.parse(readFileSync(REPORT_PATH, 'utf8'));
    assert.equal(mismatchReport.equal, false, 'mismatch report must flag inequality');
    assert.ok(Array.isArray(mismatchReport.diff) && mismatchReport.diff.length > 0);
    assert.equal(mismatchReport.diff[0].artifact, 'orders');
  } finally {
    writeFileSync(ordersPath, originalOrders);
  }
});
