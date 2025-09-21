import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { strict as assert } from 'node:assert';

const parityOutDir = 'out/0.4/pilot-l0/parity-test';

function runScript(script) {
  const result = spawnSync('node', [script], {
    stdio: 'inherit',
    env: { ...process.env, TF_PILOT_OUT_DIR: parityOutDir },
  });
  assert.equal(result.status, 0, `${script} exited with ${result.status}`);
}

test('pilot pipeline parity matches manual runner deterministically', () => {
  runScript('scripts/pilot-build-run.mjs');
  runScript('scripts/pilot-handwritten.mjs');
  runScript('scripts/pilot-parity.mjs');

  const reportPath = 'out/0.4/parity/report.json';
  const rawReport = readFileSync(reportPath, 'utf8');
  const report = JSON.parse(rawReport);
  assert.equal(report.equal, true, 'generated and manual artifacts diverged');
  assert.deepEqual(report.diff, []);

  runScript('scripts/pilot-parity.mjs');
  const rerunRaw = readFileSync(reportPath, 'utf8');
  assert.equal(rerunRaw, rawReport, 'report.json should be deterministic across runs');
});
