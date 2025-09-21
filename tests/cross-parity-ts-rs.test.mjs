import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const SCRIPT = path.join(ROOT, 'scripts/cross-parity-ts-rs.mjs');
const FLOW = path.join(ROOT, 'examples/flows/run_publish.tf');
const REPORT = path.join(ROOT, 'out/0.4/parity/ts-rs/report.json');

test('cross parity script produces report', () => {
  fs.rmSync(REPORT, { force: true });
  const env = { ...process.env };
  delete env.LOCAL_RUST;
  const result = spawnSync(process.execPath, [SCRIPT, FLOW], { cwd: ROOT, stdio: 'inherit', env });
  assert.equal(result.status, 0, 'cross parity script should exit 0');
  assert.ok(fs.existsSync(REPORT), 'parity report should exist');
  const report = JSON.parse(fs.readFileSync(REPORT, 'utf8'));
  assert.ok(Object.prototype.hasOwnProperty.call(report, 'equal'), 'report must include equal field');
  assert.ok(report.counts && typeof report.counts.ts === 'number');
});

test('cross parity matches under LOCAL_RUST', { skip: !process.env.LOCAL_RUST }, () => {
  const env = { ...process.env, LOCAL_RUST: '1' };
  const result = spawnSync(process.execPath, [SCRIPT, FLOW], { cwd: ROOT, stdio: 'inherit', env });
  assert.equal(result.status, 0, 'cross parity script should exit 0 with LOCAL_RUST');
  const report = JSON.parse(fs.readFileSync(REPORT, 'utf8'));
  assert.equal(report.equal, true, 'ts and rust traces should match');
});
