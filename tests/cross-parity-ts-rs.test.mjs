import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const REPORT_PATH = path.join(ROOT, 'out/0.4/parity/ts-rs/report.json');
const FLOW_PATH = path.join(ROOT, 'examples/flows/run_publish.tf');

const shouldRun = process.env.LOCAL_RUST === '1';

test('ts↔rs trace parity for run_publish (requires LOCAL_RUST=1)', async (t) => {
  if (!shouldRun) {
    t.skip('LOCAL_RUST=1 required for parity run');
    return;
  }

  const result = spawnSync(process.execPath, ['scripts/cross-parity-ts-rs.mjs', FLOW_PATH], {
    cwd: ROOT,
    stdio: 'inherit',
    env: process.env,
  });
  assert.equal(result.status, 0, 'cross-parity script should succeed');
  const reportRaw = fs.readFileSync(REPORT_PATH, 'utf8');
  const report = JSON.parse(reportRaw);
  assert.equal(report.equal, true, 'expected ts and rs traces to match');
});
