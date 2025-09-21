import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { strict as assert } from 'node:assert';

const baseOut = 'out/0.4/tests/pilot-parity';
const pilotOutRel = `${baseOut}/pilot-l0`;
const reportPath = `${baseOut}/parity/report.json`;

function runScript(script) {
  const env = { ...process.env, TF_PILOT_OUT_DIR: pilotOutRel };
  return spawnSync('node', [`scripts/${script}`], { stdio: 'inherit', env });
}

test('pilot pipeline parity with manual runner', () => {
  const build = runScript('pilot-build-run.mjs');
  assert.equal(build.status, 0, 'pilot-build-run.mjs exited with non-zero status');

  const manual = runScript('pilot-handwritten.mjs');
  assert.equal(manual.status, 0, 'pilot-handwritten.mjs exited with non-zero status');

  const parity = runScript('pilot-parity.mjs');
  assert.equal(parity.status, 0, 'pilot-parity.mjs exited with non-zero status');

  const reportRaw1 = readFileSync(reportPath, 'utf8');
  const report1 = JSON.parse(reportRaw1);
  assert.equal(report1.equal, true, 'expected parity report equal=true');

  const parityRepeat = runScript('pilot-parity.mjs');
  assert.equal(parityRepeat.status, 0, 'pilot-parity.mjs repeat exited with non-zero status');

  const reportRaw2 = readFileSync(reportPath, 'utf8');
  assert.equal(reportRaw2, reportRaw1, 'parity report changed between runs');

  const report2 = JSON.parse(reportRaw2);
  assert.equal(report2.equal, true, 'repeat parity report should remain equal');
});
