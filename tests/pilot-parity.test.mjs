import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { strict as assert } from 'node:assert';

const workdir = 'out/0.4/pilot-parity-test';

function runScript(name) {
  const result = spawnSync('node', [name], {
    stdio: 'inherit',
    env: { ...process.env, TF_PILOT_WORKDIR: workdir },
  });
  assert.equal(result.status, 0, `${name} exited with ${result.status}`);
}

test('pilot pipeline matches handwritten runner', () => {
  runScript('scripts/pilot-build-run.mjs');
  runScript('scripts/pilot-handwritten.mjs');
  runScript('scripts/pilot-parity.mjs');

  const reportPath = join(workdir, 'parity', 'report.json');
  const firstReport = readFileSync(reportPath, 'utf8');
  const parsed = JSON.parse(firstReport);
  assert.equal(parsed.equal, true, 'parity report should indicate equality');

  runScript('scripts/pilot-parity.mjs');
  const secondReport = readFileSync(reportPath, 'utf8');
  assert.equal(secondReport, firstReport, 'parity report must be stable across runs');
});
