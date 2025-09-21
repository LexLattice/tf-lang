import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync, rmSync } from 'node:fs';
import { strict as assert } from 'node:assert';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const PILOT_OUT = path.join(ROOT, 'out', '0.4', 'pilot-l0', 'parity-test');
const PARITY_OUT = path.join(ROOT, 'out', '0.4', 'parity', 'parity-test');

function runScript(script) {
  return spawnSync('node', [script], {
    stdio: 'inherit',
    env: {
      ...process.env,
      PILOT_OUT_DIR: PILOT_OUT,
      PILOT_PARITY_DIR: PARITY_OUT,
    },
  });
}

test('pilot build parity against manual runner', () => {
  rmSync(PILOT_OUT, { recursive: true, force: true });
  rmSync(PARITY_OUT, { recursive: true, force: true });

  const build = runScript('scripts/pilot-build-run.mjs');
  assert.equal(build.status, 0, 'pilot-build-run should exit cleanly');

  const manual = runScript('scripts/pilot-handwritten.mjs');
  assert.equal(manual.status, 0, 'pilot-handwritten should exit cleanly');

  const parity = () => runScript('scripts/pilot-parity.mjs');

  const first = parity();
  assert.equal(first.status, 0, 'pilot-parity should report success');

  const reportPath = path.join(PARITY_OUT, 'report.json');
  const reportRaw1 = readFileSync(reportPath, 'utf8');
  const report1 = JSON.parse(reportRaw1);
  assert.equal(report1.equal, true, 'parity report should mark equality');
  assert.deepEqual(report1.diff, [], 'parity diff should be empty');

  const second = parity();
  assert.equal(second.status, 0, 'pilot-parity rerun should succeed');

  const reportRaw2 = readFileSync(reportPath, 'utf8');
  assert.equal(reportRaw2, reportRaw1, 'parity report should be stable across runs');
});
