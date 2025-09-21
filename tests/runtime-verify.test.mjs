import test from 'node:test';
import { strict as assert } from 'node:assert';
import { spawnSync } from 'node:child_process';
import { readFileSync, mkdirSync, openSync, closeSync, unlinkSync } from 'node:fs';
import { promises as fsp } from 'node:fs';
import { setTimeout as delay } from 'node:timers/promises';

const pilotOutDir = 'out/0.4/pilot-l0/runtime-verify';
const pilotLockPath = `${pilotOutDir}/.test-lock`;
const lockMaxAttempts = 200;
const lockDelayMs = 50;

async function acquirePilotLock() {
  mkdirSync(pilotOutDir, { recursive: true });
  for (let attempt = 0; attempt < lockMaxAttempts; attempt += 1) {
    try {
      const fd = openSync(pilotLockPath, 'wx');
      closeSync(fd);
      return () => {
        try {
          unlinkSync(pilotLockPath);
        } catch (err) {
          if (err?.code !== 'ENOENT') throw err;
        }
      };
    } catch (err) {
      if (err?.code !== 'EEXIST') throw err;
    }
    await delay(lockDelayMs);
  }
  throw new Error('unable to acquire pilot lock');
}

function mutateHash(hash) {
  if (typeof hash !== 'string' || hash.length === 0) return 'sha256:deadbeef';
  const last = hash.slice(-1);
  const replacement = last === '0' ? '1' : last === '1' ? '2' : '0';
  return hash.slice(0, -1) + replacement;
}

function withPilotEnv(extra = {}) {
  return {
    ...process.env,
    TF_PROVENANCE: '1',
    TF_FIXED_TS: '1750000000000',
    PILOT_OUT_DIR: pilotOutDir,
    ...extra,
  };
}

function runPilotBuild() {
  return spawnSync(process.execPath, ['scripts/pilot-build-run.mjs'], {
    env: withPilotEnv(),
    stdio: 'pipe',
    encoding: 'utf8',
  });
}

function runRuntimeVerify(args = []) {
  return spawnSync(process.execPath, ['scripts/runtime-verify.mjs', ...args], {
    env: withPilotEnv(),
    stdio: 'pipe',
    encoding: 'utf8',
  });
}

const reportPath = 'out/0.4/verify/test/report.json';
const statusPath = `${pilotOutDir}/status.json`;

test('runtime verify CLI validates and verifies pilot flow', { concurrency: false }, async () => {
  const releaseLock = await acquirePilotLock();
  try {
    const build = runPilotBuild();
    assert.equal(build.status, 0, build.stderr);

    const first = runRuntimeVerify(['--flow', 'pilot', '--out', reportPath]);
    assert.equal(first.status, 0, first.stderr);
    const reportRaw1 = readFileSync(reportPath, 'utf8');
    const report1 = JSON.parse(reportRaw1);
    assert.equal(report1.ok, true);
    assert.equal(report1.steps.validate, true);
    assert.equal(report1.steps.verify, true);

    const second = runRuntimeVerify(['--flow', 'pilot', '--out', reportPath]);
    assert.equal(second.status, 0, second.stderr);
    const reportRaw2 = readFileSync(reportPath, 'utf8');
    assert.equal(reportRaw2, reportRaw1);

    const originalStatusRaw = await fsp.readFile(statusPath, 'utf8');
    const status = JSON.parse(originalStatusRaw);
    status.provenance.manifest_hash = mutateHash(status.provenance.manifest_hash);
    await fsp.writeFile(statusPath, JSON.stringify(status, null, 2) + '\n');
    try {
      const failed = runRuntimeVerify(['--flow', 'pilot', '--out', reportPath]);
      assert.notEqual(failed.status, 0);
      const failedRaw = readFileSync(reportPath, 'utf8');
      const failedReport = JSON.parse(failedRaw);
      assert.equal(failedReport.ok, false);
      assert.equal(failedReport.steps.validate, true);
      assert.equal(failedReport.steps.verify, false);
      assert.ok(Array.isArray(failedReport.issues));
      assert.ok(failedReport.issues.some((issue) => typeof issue === 'string' && issue.includes('manifest_hash')));
    } finally {
      await fsp.writeFile(statusPath, originalStatusRaw);
    }
  } finally {
    releaseLock();
  }
});
