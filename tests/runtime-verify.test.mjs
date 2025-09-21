import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile, writeFile, mkdir, open as openFile, unlink } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { setTimeout as delay } from 'node:timers/promises';

const rootDir = dirname(fileURLToPath(new URL('../package.json', import.meta.url)));
const lockPath = join(rootDir, 'out', '0.4', 'pilot-l0', '.test-lock');
const lockDelayMs = 50;
const lockMaxAttempts = 200;

function runNode(args, { env } = {}) {
  const result = spawnSync(process.execPath, args, {
    cwd: rootDir,
    env: env ? { ...process.env, ...env } : process.env,
    encoding: 'utf8',
    maxBuffer: 10 * 1024 * 1024,
  });
  return {
    status: typeof result.status === 'number' ? result.status : result.error?.code ?? -1,
    stdout: result.stdout || '',
    stderr: result.stderr || '',
  };
}

function flipHash(value) {
  if (typeof value !== 'string' || value.length === 0) return value;
  const last = value[value.length - 1];
  const replacement = last === '0' ? '1' : '0';
  return value.slice(0, -1) + replacement;
}

async function acquirePilotLock() {
  await mkdir(join(rootDir, 'out', '0.4', 'pilot-l0'), { recursive: true });
  for (let attempt = 0; attempt < lockMaxAttempts; attempt += 1) {
    try {
      const handle = await openFile(lockPath, 'wx');
      await handle.close();
      return async () => {
        try {
          await unlink(lockPath);
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

test('runtime verify pilot flow', async () => {
  const releaseLock = await acquirePilotLock();
  const pilotOutDir = join(rootDir, 'out', '0.4', 'verify-test', 'pilot');
  const statusPath = join(pilotOutDir, 'status.json');
  let statusOriginal = null;
  const pilotEnv = {
    TF_PROVENANCE: '1',
    TF_FIXED_TS: '1750000000000',
    PILOT_OUT_DIR: pilotOutDir,
  };
  try {
    const pilotRun = runNode(['scripts/pilot-build-run.mjs'], { env: pilotEnv });
    assert.equal(pilotRun.status, 0, pilotRun.stderr || pilotRun.stdout);

    const irPath = join(pilotOutDir, 'pilot_min.ir.json');
    const manifestPath = join(pilotOutDir, 'pilot_min.manifest.json');
    const tracePath = join(pilotOutDir, 'trace.jsonl');

    const reportPath = join(rootDir, 'out', '0.4', 'verify', 'pilot-test', 'report.json');
    const verifyOk = runNode([
      'scripts/runtime-verify.mjs',
      '--ir',
      irPath,
      '--manifest',
      manifestPath,
      '--status',
      statusPath,
      '--trace',
      tracePath,
      '--out',
      reportPath,
    ]);
    const reportRaw = await readFile(reportPath, 'utf8');
    const report = JSON.parse(reportRaw);
    assert.equal(verifyOk.status, 0, verifyOk.stderr || verifyOk.stdout || reportRaw);
    assert.equal(report.ok, true);
    assert.equal(report.steps?.validate, true);
    assert.equal(report.steps?.verify, true);

    const verifyAgain = runNode([
      'scripts/runtime-verify.mjs',
      '--ir',
      irPath,
      '--manifest',
      manifestPath,
      '--status',
      statusPath,
      '--trace',
      tracePath,
      '--out',
      reportPath,
    ]);
    const reportRawAgain = await readFile(reportPath, 'utf8');
    assert.equal(verifyAgain.status, 0, verifyAgain.stderr || verifyAgain.stdout || reportRawAgain);
    assert.equal(reportRawAgain, reportRaw);

    statusOriginal = await readFile(statusPath, 'utf8');
    const status = JSON.parse(statusOriginal);
    assert.ok(status?.provenance?.manifest_hash, 'expected provenance.manifest_hash');
    status.provenance.manifest_hash = flipHash(status.provenance.manifest_hash);
    await writeFile(statusPath, JSON.stringify(status, null, 2) + '\n');

    const tamperedPath = join(rootDir, 'out', '0.4', 'verify', 'pilot-test', 'report-tampered.json');
    const verifyTampered = runNode([
      'scripts/runtime-verify.mjs',
      '--ir',
      irPath,
      '--manifest',
      manifestPath,
      '--status',
      statusPath,
      '--trace',
      tracePath,
      '--out',
      tamperedPath,
    ]);
    const tamperedRaw = await readFile(tamperedPath, 'utf8');
    const tampered = JSON.parse(tamperedRaw);
    assert.notEqual(verifyTampered.status, 0, verifyTampered.stderr || verifyTampered.stdout || tamperedRaw);
    assert.equal(tampered.ok, false);
    assert.equal(tampered.steps?.validate, true);
    assert.equal(tampered.steps?.verify, false);
    const issues = Array.isArray(tampered.issues) ? tampered.issues : [];
    const hit = issues.some((entry) => {
      const text = typeof entry === 'string' ? entry : JSON.stringify(entry);
      return text.includes('manifest_hash');
    });
    assert.equal(hit, true, `expected manifest_hash in issues, saw ${JSON.stringify(issues)}`);
  } finally {
    if (statusOriginal !== null) {
      await writeFile(statusPath, statusOriginal);
    }
    await releaseLock();
  }
});
