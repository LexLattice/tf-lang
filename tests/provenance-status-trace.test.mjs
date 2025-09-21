import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

test('pilot provenance is captured in status, trace, and verification', () => {
  const run = spawnSync(process.execPath, ['scripts/pilot-build-run.mjs'], {
    env: { ...process.env, TF_PROVENANCE: '1' },
    encoding: 'utf8',
  });
  assert.equal(run.status, 0, run.stderr || run.stdout);

  const outDir = resolve('out/0.4/pilot-l0');
  const statusPath = resolve(outDir, 'status.json');
  const tracePath = resolve(outDir, 'trace.jsonl');
  const manifestPath = resolve(outDir, 'pilot_min.manifest.json');
  const irPath = resolve(outDir, 'pilot_min.ir.json');

  const status = JSON.parse(readFileSync(statusPath, 'utf8'));
  assert.equal(status.ok, true);
  assert.ok(status.provenance, 'expected status.provenance');
  const prov = status.provenance;
  assert.match(prov.ir_hash, /^sha256:/);
  assert.match(prov.manifest_hash, /^sha256:/);
  assert.match(prov.catalog_hash, /^sha256:/);
  assert.equal(prov.caps_source, 'file');
  assert.deepEqual(prov.caps_effects, ['Network.Out', 'Observability', 'Pure', 'Storage.Write']);

  const traceRaw = readFileSync(tracePath, 'utf8');
  const validate = spawnSync(process.execPath, [
    'scripts/validate-trace.mjs',
    '--require-meta',
    '--ir',
    prov.ir_hash,
    '--manifest',
    prov.manifest_hash,
    '--catalog',
    prov.catalog_hash,
  ], {
    encoding: 'utf8',
    input: traceRaw,
  });
  assert.equal(validate.status, 0, validate.stderr);
  const validateSummary = JSON.parse(validate.stdout.trim());
  assert.equal(validate.stdout.trim(), JSON.stringify(validateSummary));
  assert.equal(validateSummary.ok, true);
  assert.equal(validateSummary.invalid, 0);
  assert.equal(validateSummary.meta_checked, true);
  assert.ok(validateSummary.total > 0);

  const verifyArgs = [
    '--ir', irPath,
    '--trace', tracePath,
    '--status', statusPath,
    '--manifest', manifestPath,
  ];
  const verify = spawnSync(process.execPath, ['packages/tf-compose/bin/tf-verify-trace.mjs', ...verifyArgs], {
    encoding: 'utf8',
  });
  assert.equal(verify.status, 0, verify.stderr);
  const verifySummary = JSON.parse(verify.stdout.trim());
  assert.equal(verify.stdout.trim(), JSON.stringify(verifySummary));
  assert.equal(verifySummary.ok, true);
  assert.equal(verifySummary.counts.meta_mismatches, 0);
  assert.equal(verifySummary.counts.provenance_mismatches, 0);

  const badVerify = spawnSync(
    process.execPath,
    ['packages/tf-compose/bin/tf-verify-trace.mjs', ...verifyArgs, '--manifest-hash', 'sha256:deadbeef'],
    { encoding: 'utf8' },
  );
  assert.equal(badVerify.status, 1, badVerify.stderr || badVerify.stdout);
  const badSummary = JSON.parse(badVerify.stdout.trim());
  assert.equal(badVerify.stdout.trim(), JSON.stringify(badSummary));
  assert.equal(badSummary.ok, false);
  assert.ok(badSummary.issues.some((issue) => issue.includes('manifest hash mismatch')));
});
