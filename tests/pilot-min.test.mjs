// @tf-test kind=product area=runtime speed=medium deps=node
import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync, mkdirSync, openSync, closeSync, unlinkSync } from 'node:fs';
import { strict as assert } from 'node:assert';
import { setTimeout as delay } from 'node:timers/promises';

async function readJsonWithRetry(path) {
  for (let attempt = 0; attempt < 5; attempt += 1) {
    try {
      const raw = readFileSync(path, 'utf8');
      if (!raw) throw new Error('empty');
      return JSON.parse(raw);
    } catch (err) {
      if (attempt === 4) throw err;
      await delay(50);
    }
  }
  throw new Error(`unable to read ${path}`);
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

test('pilot_min flow runs and summarizes deterministically', { concurrency: false }, async () => {
  const releaseLock = await acquirePilotLock();
  const run = () =>
    spawnSync(process.execPath, ['scripts/pilot-min.mjs'], {
      stdio: 'pipe',
      encoding: 'utf8',
    });

  const first = run();
  try {
    assert.equal(first.status, 0, first.stderr);

    const statusPath = 'out/0.4/pilot-l0/status.json';
    const summaryPath = 'out/0.4/pilot-l0/summary.json';

    const status = await readJsonWithRetry(statusPath);
    const summary = await readJsonWithRetry(summaryPath);

    assert.equal(status.ok, true);
    assert.ok(status.ops >= 2);
    assert.ok(Array.isArray(status.effects));
    const provenance = status.provenance;
    assert.ok(provenance);
    assert.equal(typeof provenance.ir_hash, 'string');
    assert.equal(typeof provenance.manifest_hash, 'string');
    assert.equal(typeof provenance.catalog_hash, 'string');
    assert.ok(Array.isArray(provenance.caps_effects));
    assert.equal(typeof provenance.caps_source, 'string');
    const allowed = new Set(provenance.caps_effects);
    assert.ok(status.effects.some((effect) => effect === 'Network.Out'));
    assert.ok(status.effects.some((effect) => effect.startsWith('Storage.Write')));
    for (const effect of status.effects) {
      const base = effect.split('.')[0];
      assert.ok(allowed.has(effect) || allowed.has(base));
    }

    assert.ok(summary.total >= 3);
    assert.ok(summary.by_prim['tf:network/publish@1'] >= 1);
    assert.ok(summary.by_prim['tf:resource/write-object@1'] >= 1);

    const summaryRaw1 = readFileSync(summaryPath, 'utf8');

    const second = run();
    assert.equal(second.status, 0, second.stderr);

    const summaryRaw2 = readFileSync(summaryPath, 'utf8');
    assert.equal(summaryRaw2, summaryRaw1);

    const summaryRepeat = JSON.parse(summaryRaw2);
    assert.ok(summaryRepeat.total >= 3);
    assert.ok(summaryRepeat.by_prim['tf:network/publish@1'] >= 1);
    assert.ok(summaryRepeat.by_prim['tf:resource/write-object@1'] >= 1);
  } finally {
    releaseLock();
  }
});
