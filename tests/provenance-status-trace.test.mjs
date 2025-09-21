import test from 'node:test';
import { strict as assert } from 'node:assert';
import { spawnSync } from 'node:child_process';
import { readFileSync, mkdirSync, openSync, closeSync, unlinkSync } from 'node:fs';
import { setTimeout as delay } from 'node:timers/promises';

const statusPath = 'out/0.4/pilot-l0/status.json';
const tracePath = 'out/0.4/pilot-l0/trace.jsonl';
const irPath = 'out/0.4/pilot-l0/pilot_min.ir.json';
const manifestPath = 'out/0.4/pilot-l0/pilot_min.manifest.json';

function mutateHash(hash) {
  if (typeof hash !== 'string' || hash.length === 0) return 'sha256:deadbeef';
  const last = hash.slice(-1);
  const replacement = last === '0' ? '1' : last === '1' ? '2' : '0';
  return hash.slice(0, -1) + replacement;
}

const lockPath = 'out/0.4/pilot-l0/.test-lock';
const lockMaxAttempts = 200;
const lockDelayMs = 50;

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

test('pilot run captures provenance and verifies trace', { concurrency: false }, async () => {
  const releaseLock = await acquirePilotLock();
  try {
    const run = spawnSync(process.execPath, ['scripts/pilot-build-run.mjs'], {
      env: { ...process.env, TF_PROVENANCE: '1' },
      stdio: 'pipe',
      encoding: 'utf8',
    });
    assert.equal(run.status, 0, run.stderr);

    const statusRawFirst = readFileSync(statusPath, 'utf8');
    const status = JSON.parse(statusRawFirst);
    assert.ok(status.provenance, 'expected provenance block in status');
    const provenance = status.provenance;
    assert.equal(typeof provenance.ir_hash, 'string');
    assert.equal(typeof provenance.manifest_hash, 'string');
    assert.equal(typeof provenance.catalog_hash, 'string');
    assert.equal(typeof provenance.caps_source, 'string');
    assert.ok(Array.isArray(provenance.caps_effects));
    const allowedEffects = new Set(provenance.caps_effects);
    for (const effect of status.effects) {
      const base = effect.split('.')[0];
      assert.ok(allowedEffects.has(effect) || allowedEffects.has(base));
    }

    const traceRaw = readFileSync(tracePath, 'utf8');
    const traceRawFirst = traceRaw;
    const validate = spawnSync(
      process.execPath,
      [
        'scripts/validate-trace.mjs',
        '--require-meta',
        '--ir',
        provenance.ir_hash,
        '--manifest',
        provenance.manifest_hash,
        '--catalog',
        provenance.catalog_hash,
      ],
      { input: traceRaw, encoding: 'utf8' },
    );
    assert.equal(validate.status, 0, validate.stderr);
    const validateSummary = JSON.parse(validate.stdout.trim());
    assert.equal(validateSummary.ok, true);
    assert.equal(validateSummary.meta_checked, true);

    const verify = spawnSync(
      process.execPath,
      [
        'packages/tf-compose/bin/tf-verify-trace.mjs',
        '--ir',
        irPath,
        '--trace',
        tracePath,
        '--status',
        statusPath,
        '--manifest',
        manifestPath,
      ],
      { encoding: 'utf8' },
    );
    assert.equal(verify.status, 0, verify.stderr);
    const verifyResult = JSON.parse(verify.stdout.trim());
    assert.equal(verifyResult.ok, true);

    const verifyBad = spawnSync(
      process.execPath,
      [
        'packages/tf-compose/bin/tf-verify-trace.mjs',
        '--ir',
        irPath,
        '--trace',
        tracePath,
        '--status',
        statusPath,
        '--manifest',
        manifestPath,
        '--manifest-hash',
        mutateHash(provenance.manifest_hash),
      ],
      { encoding: 'utf8' },
    );
    assert.notEqual(verifyBad.status, 0);
    const badResult = JSON.parse(verifyBad.stdout.trim());
    assert.equal(badResult.ok, false);
    assert.ok(badResult.issues.some((issue) => issue.includes('hash_mismatch:manifest_hash')));

    const rerun = spawnSync(process.execPath, ['scripts/pilot-build-run.mjs'], {
      env: { ...process.env, TF_PROVENANCE: '1' },
      stdio: 'pipe',
      encoding: 'utf8',
    });
    assert.equal(rerun.status, 0, rerun.stderr);
    const statusRawSecond = readFileSync(statusPath, 'utf8');
    const traceRawSecond = readFileSync(tracePath, 'utf8');
    assert.equal(statusRawSecond, statusRawFirst, 'status.json should be deterministic');
    assert.equal(traceRawSecond, traceRawFirst, 'trace.jsonl should be deterministic');
  } finally {
    releaseLock();
  }
});
