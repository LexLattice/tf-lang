import test from 'node:test';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import assert from 'node:assert/strict';

test('pilot_min flow runs and summarizes', () => {
  const r = spawnSync('node', ['scripts/pilot-min.mjs'], { stdio: 'inherit' });
  assert.equal(r.status, 0);

  const status = JSON.parse(readFileSync('out/0.4/pilot-l0/status.json', 'utf8'));
  const summary = JSON.parse(readFileSync('out/0.4/pilot-l0/summary.json', 'utf8'));

  assert.equal(status.ok, true);
  assert.ok(status.ops >= 2);
  assert.ok(Array.isArray(status.effects));
  // At least these effects should appear
  assert.ok(status.effects.includes('Network.Out'));
  assert.ok(status.effects.includes('Storage.Write'));

  // Summary sanity
  assert.ok(summary.total >= 2);
  assert.ok(summary.by_prim['tf:network/publish@1'] >= 1);
});
