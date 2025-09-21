import test from 'node:test';
import { strict as assert } from 'node:assert';
import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdirSync, openSync, closeSync, unlinkSync } from 'node:fs';
import { setTimeout as delay } from 'node:timers/promises';

const pilotOutDir = 'out/0.4/pilot-l0/runtime-verify';
const reportPath = 'out/0.4/verify/pilot/report.json';
const badReportPath = 'out/0.4/verify/pilot/report.bad.json';
const statusPath = `${pilotOutDir}/status.json`;

const lockPath = 'out/0.4/pilot-l0/.test-lock';
const lockMaxAttempts = 200;
const lockDelayMs = 50;

function mutateHash(hash) {
  if (typeof hash !== 'string' || hash.length === 0) return 'sha256:deadbeef';
  const last = hash.slice(-1);
  const replacement = last === '0' ? '1' : last === '1' ? '2' : '0';
  return hash.slice(0, -1) + replacement;
}

async function acquirePilotLock() {
  mkdirSync('out/0.4/pilot-l0', { recursive: true });
  for (let attempt = 0; attempt < lockMaxAttempts; attempt += 1) {
    try {
      const fd = openSync(lockPath, 'wx');
      closeSync(fd);
      return () => {
        try {
          unlinkSync(lockPath);
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

test('runtime verify pilot flow', { concurrency: false }, async () => {
  const releaseLock = await acquirePilotLock();
  try {
    const buildEnv = {
      ...process.env,
      TF_PROVENANCE: '1',
      TF_FIXED_TS: '1750000000000',
      PILOT_OUT_DIR: pilotOutDir,
    };
    const build = spawnSync(process.execPath, ['scripts/pilot-build-run.mjs'], {
      env: buildEnv,
      encoding: 'utf8',
    });
    assert.equal(build.status, 0, build.stderr);

    const verifyEnv = { ...process.env, PILOT_OUT_DIR: pilotOutDir };
    const firstRun = spawnSync(
      process.execPath,
      ['scripts/runtime-verify.mjs', '--flow', 'pilot', '--out', reportPath],
      { env: verifyEnv, encoding: 'utf8' },
    );
    assert.equal(firstRun.status, 0, firstRun.stderr);
    const reportRawFirst = readFileSync(reportPath, 'utf8').trim();
    const reportFirst = JSON.parse(reportRawFirst);
    assert.equal(reportFirst.ok, true);
    assert.equal(reportFirst.steps.validate, true);
    assert.equal(reportFirst.steps.verify, true);

    const secondRun = spawnSync(
      process.execPath,
      ['scripts/runtime-verify.mjs', '--flow', 'pilot', '--out', reportPath],
      { env: verifyEnv, encoding: 'utf8' },
    );
    assert.equal(secondRun.status, 0, secondRun.stderr);
    const reportRawSecond = readFileSync(reportPath, 'utf8').trim();
    assert.equal(reportRawSecond, reportRawFirst, 'report output should be deterministic');

    const originalStatus = readFileSync(statusPath, 'utf8');
    const tampered = JSON.parse(originalStatus);
    assert.ok(tampered?.provenance?.manifest_hash, 'status must contain manifest hash');
    tampered.provenance.manifest_hash = mutateHash(tampered.provenance.manifest_hash);

    try {
      writeFileSync(statusPath, JSON.stringify(tampered, null, 2) + '\n');
      const badRun = spawnSync(
        process.execPath,
        ['scripts/runtime-verify.mjs', '--flow', 'pilot', '--out', badReportPath],
        { env: verifyEnv, encoding: 'utf8' },
      );
      assert.notEqual(badRun.status, 0, 'tampered manifest hash should fail verify');
      const badReportRaw = readFileSync(badReportPath, 'utf8').trim();
      const badReport = JSON.parse(badReportRaw);
      assert.equal(badReport.ok, false);
      assert.ok(Array.isArray(badReport.issues), 'expected issues array');
      assert.ok(
        badReport.issues.some((issue) => {
          if (typeof issue === 'string') return issue.includes('manifest_hash');
          if (issue && typeof issue === 'object') {
            return Object.values(issue).some((value) =>
              typeof value === 'string' && value.includes('manifest_hash'),
            );
          }
          return false;
        }),
        'issues should reference manifest_hash',
      );
    } finally {
      writeFileSync(statusPath, originalStatus);
    }
  } finally {
    releaseLock();
  }
});
