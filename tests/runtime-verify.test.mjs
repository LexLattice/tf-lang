import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { strict as assert } from 'node:assert';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const runtimeVerifyCli = fileURLToPath(new URL('../scripts/runtime-verify.mjs', import.meta.url));
const pilotBuildScript = fileURLToPath(new URL('../scripts/pilot-build-run.mjs', import.meta.url));

function mutateHash(hash) {
  if (typeof hash !== 'string' || hash.length === 0) return 'sha256:deadbeef';
  const last = hash.slice(-1);
  const replacement = last === '0' ? '1' : last === '1' ? '2' : '0';
  return hash.slice(0, -1) + replacement;
}

test('runtime verify pipeline is deterministic and detects provenance drift', { concurrency: false }, async () => {
  let originalStatusRaw = null;
  const pilotOutDir = 'out/0.4/pilot-l0/runtime-verify-test';
  const statusPath = join(pilotOutDir, 'status.json');
  const env = {
    ...process.env,
    TF_PROVENANCE: '1',
    TF_FIXED_TS: '1750000000000',
    PILOT_OUT_DIR: pilotOutDir,
  };
  const verifyDir = 'out/0.4/verify/pilot-runtime-test';
  try {
    const build = spawnSync(process.execPath, [pilotBuildScript], {
      stdio: 'pipe',
      encoding: 'utf8',
      env,
    });
    assert.equal(build.status, 0, build.stderr);

    const reportPath = join(verifyDir, 'report.json');
    const runVerify = () =>
      spawnSync(process.execPath, [runtimeVerifyCli, '--flow', 'pilot', '--out', reportPath], {
        stdio: 'pipe',
        encoding: 'utf8',
        env,
      });

    const first = runVerify();
    assert.equal(first.status, 0, first.stderr);
    const reportRaw1 = readFileSync(reportPath, 'utf8');
    const report1 = JSON.parse(reportRaw1);
    assert.equal(report1.ok, true);
    assert.deepEqual(report1.steps, { validate: true, verify: true });

    const second = runVerify();
    assert.equal(second.status, 0, second.stderr);
    const reportRaw2 = readFileSync(reportPath, 'utf8');
    assert.equal(reportRaw2, reportRaw1);

    originalStatusRaw = readFileSync(statusPath, 'utf8');
    const status = JSON.parse(originalStatusRaw);
    if (status?.provenance && typeof status.provenance.manifest_hash === 'string') {
      status.provenance.manifest_hash = mutateHash(status.provenance.manifest_hash);
      writeFileSync(statusPath, JSON.stringify(status, null, 2) + '\n');
    } else {
      throw new Error('status missing provenance.manifest_hash');
    }

    const failReportPath = join(verifyDir, 'report-fail.json');
    const failure = spawnSync(process.execPath, [runtimeVerifyCli, '--flow', 'pilot', '--out', failReportPath], {
      stdio: 'pipe',
      encoding: 'utf8',
      env,
    });
    assert.notEqual(failure.status, 0, failure.stderr);
    const failReportRaw = readFileSync(failReportPath, 'utf8');
    const failReport = JSON.parse(failReportRaw);
    assert.equal(failReport.ok, false);
    assert.equal(failReport.steps.verify, false);
    assert.ok(JSON.stringify(failReport.issues || []).includes('manifest_hash'));
  } finally {
    if (originalStatusRaw !== null) {
      writeFileSync(statusPath, originalStatusRaw);
    }
  }
});
