import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { strict as assert } from 'node:assert';

test('pilot_min flow runs and summarizes deterministically', () => {
  const run = () => spawnSync('node', ['scripts/pilot-min.mjs'], { stdio: 'inherit' });

  const first = run();
  assert.equal(first.status, 0);

  const statusPath = 'out/0.4/pilot-l0/status.json';
  const summaryPath = 'out/0.4/pilot-l0/summary.json';

  const status = JSON.parse(readFileSync(statusPath, 'utf8'));
  const summary = JSON.parse(readFileSync(summaryPath, 'utf8'));

  assert.equal(status.ok, true);
  assert.ok(status.ops >= 2);
  assert.ok(Array.isArray(status.effects));
  assert.ok(status.effects.includes('Network.Out'));
  assert.ok(status.effects.includes('Storage.Write'));

  assert.ok(summary.total >= 3);
  assert.ok(summary.by_prim['tf:network/publish@1'] >= 1);
  assert.ok(summary.by_prim['tf:resource/write-object@1'] >= 1);

  const summaryRaw1 = readFileSync(summaryPath, 'utf8');

  const second = run();
  assert.equal(second.status, 0);

  const summaryRaw2 = readFileSync(summaryPath, 'utf8');
  assert.equal(summaryRaw2, summaryRaw1);

  const summaryRepeat = JSON.parse(summaryRaw2);
  assert.ok(summaryRepeat.total >= 3);
  assert.ok(summaryRepeat.by_prim['tf:network/publish@1'] >= 1);
  assert.ok(summaryRepeat.by_prim['tf:resource/write-object@1'] >= 1);
});
