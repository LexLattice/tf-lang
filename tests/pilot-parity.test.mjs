// @tf-test kind=parity area=runtime speed=heavy deps=node

import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import { strict as assert } from 'node:assert';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const PILOT_OUT = path.join(ROOT, 'out', '0.4', 'pilot-l0', 'parity-test');
const PARITY_OUT = path.join(ROOT, 'out', '0.4', 'parity', 'parity-test');
const FIXED_TS = '1750000000000';

function envWithOverrides() {
  return {
    ...process.env,
    PILOT_OUT_DIR: PILOT_OUT,
    PILOT_PARITY_DIR: PARITY_OUT,
    TF_FIXED_TS: FIXED_TS,
  };
}

function runPnpm(script) {
  return spawnSync('pnpm', ['run', script], {
    stdio: 'inherit',
    cwd: ROOT,
    env: envWithOverrides(),
  });
}

function runScript(script) {
  return spawnSync('node', [script], {
    stdio: 'inherit',
    cwd: ROOT,
    env: envWithOverrides(),
  });
}

test('pilot build parity against manual runner', () => {
  rmSync(PILOT_OUT, { recursive: true, force: true });
  rmSync(PARITY_OUT, { recursive: true, force: true });

  const firstAll = runPnpm('pilot:all');
  assert.equal(firstAll.status, 0, 'initial pilot:all run should succeed');

  const reportPath = path.join(PARITY_OUT, 'report.json');
  const reportRaw1 = readFileSync(reportPath, 'utf8');
  const report1 = JSON.parse(reportRaw1);
  assert.equal(report1.equal, true, 'parity report should mark equality');
  assert.deepEqual(report1.diff, [], 'parity diff should be empty');

  const secondAll = runPnpm('pilot:all');
  assert.equal(secondAll.status, 0, 'second pilot:all run should succeed');

  const reportRaw2 = readFileSync(reportPath, 'utf8');
  assert.equal(reportRaw2, reportRaw1, 'parity report should be stable across runs');

  const manualSummaryPath = path.join(PILOT_OUT, 'manual', 'summary.json');
  const originalSummary = readFileSync(manualSummaryPath, 'utf8');
  try {
    const tampered = JSON.parse(originalSummary);
    tampered.ops = Number(tampered.ops ?? 0) + 1;
    writeFileSync(manualSummaryPath, JSON.stringify(tampered) + '\n');
    const mismatch = runScript('scripts/pilot-parity.mjs');
    assert.equal(mismatch.status, 1, 'pilot-parity should fail on mismatched artifacts');
    const mismatchReport = JSON.parse(readFileSync(reportPath, 'utf8'));
    assert.equal(mismatchReport.equal, false, 'mismatch report must mark inequality');
    assert.ok(Array.isArray(mismatchReport.diff) && mismatchReport.diff.length > 0, 'mismatch diff must be populated');
    assert.equal(mismatchReport.diff[0].artifact, 'summary', 'diff must highlight summary mismatch');
  } finally {
    writeFileSync(manualSummaryPath, originalSummary);
  }
});
