// @tf-test kind=infra area=proofs speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, rm, mkdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

const SCRIPT = 'scripts/proofs/coverage.mjs';

function runCoverage(outRoot) {
  return spawnSync('node', [SCRIPT, '--out', outRoot], {
    encoding: 'utf8',
  });
}

test('coverage reports ok when commute stub exists', async () => {
  const workdir = await mkdtemp(path.join(tmpdir(), 'proof-coverage-'));
  const outRoot = path.join(workdir, 'out');
  const proofsDir = path.join(outRoot, '0.5', 'proofs');
  await mkdir(proofsDir, { recursive: true });
  const manifestPath = path.join(proofsDir, 'used-laws.json');
  const payload = {
    used_laws: ['commute:emit-metric-with-pure'],
  };
  await writeFile(manifestPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');

  const result = runCoverage(outRoot);
  assert.equal(result.status, 0, result.stderr || result.stdout);
  assert.equal(typeof result.stdout, 'string');
  const trimmed = result.stdout.trim();
  assert.ok(trimmed.length > 0, 'coverage script should print JSON');
  const json = JSON.parse(trimmed);
  assert.equal(json.ok, true, 'coverage should report ok');
  assert.deepEqual(json.missing, [], 'missing should be empty');
  assert.ok(
    json.covered.includes('commute:emit-metric-with-pure'),
    'covered list should include commute law',
  );

  await rm(workdir, { recursive: true, force: true });
});
