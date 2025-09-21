import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync, rmSync } from 'node:fs';
import { strict as assert } from 'node:assert';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = resolve(fileURLToPath(new URL('.', import.meta.url)), '..');
const PILOT_FULL_OUT = join(ROOT, 'out', '0.4', 'pilot-full');
const T5_FULL_OUT = join(ROOT, 'out', 't5-full');
const PARITY_OUT = join(ROOT, 'out', '0.4', 'parity', 'full');
const REPORT_PATH = join(PARITY_OUT, 'report.json');

const runFull = process.env.TF_PILOT_FULL === '1';

function run(command, args) {
  const result = spawnSync(command, args, {
    stdio: 'inherit',
    cwd: ROOT,
    env: { ...process.env, TF_PILOT_FULL: '1' },
  });
  assert.equal(result.status, 0, `${command} ${args.join(' ')} exited with ${result.status}`);
}

test('pilot full parity against t5 baseline', { skip: !runFull }, () => {
  rmSync(PILOT_FULL_OUT, { recursive: true, force: true });
  rmSync(T5_FULL_OUT, { recursive: true, force: true });
  rmSync(PARITY_OUT, { recursive: true, force: true });

  run('pnpm', ['-w', '-r', 'build']);
  run('node', ['scripts/t5-build-run.mjs']);
  run('node', ['scripts/pilot-full-build-run.mjs']);
  run('node', ['scripts/pilot-full-parity.mjs']);

  const reportRaw1 = readFileSync(REPORT_PATH, 'utf8');
  const report1 = JSON.parse(reportRaw1);
  assert.equal(report1.equal, true, 'report should indicate equality');
  assert.deepEqual(report1.diff, [], 'diff should be empty');

  run('node', ['scripts/pilot-full-parity.mjs']);
  const reportRaw2 = readFileSync(REPORT_PATH, 'utf8');
  assert.equal(reportRaw2, reportRaw1, 'report should be stable across runs');
});
