import test from 'node:test';
import { strict as assert } from 'node:assert';
import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdtempSync, existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

const rootDir = fileURLToPath(new URL('..', import.meta.url));
const scriptsDir = join(rootDir, 'scripts');
const pilotScript = join(scriptsDir, 'pilot-min.mjs');
const outDir = join(rootDir, 'out', '0.4', 'pilot-l0');
const runDir = join(outDir, 'codegen-ts', 'pilot_min');
const runScriptPath = join(runDir, 'run.mjs');
const capsPath = join(runDir, 'caps.json');
const irPath = join(outDir, 'pilot_min.ir.json');
const manifestPath = join(outDir, 'pilot_min.manifest.json');
const specCatalogPath = join(rootDir, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');
const cliPath = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-verify-trace.mjs');
const validateScript = join(rootDir, 'scripts', 'validate-trace.mjs');

function runNode(command, args, options = {}) {
  return spawnSync(process.execPath, [command, ...args], {
    stdio: options.stdio ?? 'pipe',
    input: options.input,
    encoding: 'utf8',
    env: options.env ? { ...process.env, ...options.env } : process.env,
  });
}

function ensurePilotBuild() {
  if (existsSync(runScriptPath) && existsSync(capsPath) && existsSync(irPath) && existsSync(manifestPath)) {
    return;
  }
  const result = runNode(pilotScript, []);
  assert.equal(result.status, 0, result.stderr);
}

test('status and trace include provenance fingerprints', () => {
  ensurePilotBuild();

  const tempDir = mkdtempSync(join(tmpdir(), 'tf-provenance-'));
  const tempStatusPath = join(tempDir, 'status.json');
  const tempTracePath = join(tempDir, 'trace.jsonl');

  const run = runNode(runScriptPath, ['--caps', capsPath], {
    env: {
      TF_PROVENANCE: '1',
      TF_STATUS_PATH: tempStatusPath,
      TF_TRACE_PATH: tempTracePath,
    },
  });
  assert.equal(run.status, 0, run.stderr);

  const status = JSON.parse(readFileSync(tempStatusPath, 'utf8'));
  assert.equal(status.ok, true);
  assert.ok(status.provenance, 'expected provenance in status');
  const provenance = status.provenance;
  assert.match(provenance.ir_hash, /^sha256:/);
  assert.match(provenance.manifest_hash, /^sha256:/);
  assert.match(provenance.catalog_hash, /^sha256:/);
  assert.equal(provenance.caps_source, 'file');
  assert.deepEqual(provenance.caps_effects, [
    'Network.Out',
    'Observability',
    'Pure',
    'Storage.Write',
  ]);
  assert.ok(status.effects.includes('Network.Out'));
  assert.ok(status.effects.includes('Storage.Write'));

  const traceLines = readFileSync(tempTracePath, 'utf8')
    .trim()
    .split(/\r?\n/)
    .filter(Boolean);
  assert.ok(traceLines.length > 0, 'expected trace records');
  const firstRecord = JSON.parse(traceLines[0]);
  assert.ok(firstRecord.meta, 'expected meta in trace record');
  assert.equal(firstRecord.meta.ir_hash, provenance.ir_hash);
  assert.equal(firstRecord.meta.manifest_hash, provenance.manifest_hash);
  assert.equal(firstRecord.meta.catalog_hash, provenance.catalog_hash);

  const traceData = traceLines.join('\n') + '\n';
  const validate = runNode(
    validateScript,
    [
      '--require-meta',
      '--ir',
      provenance.ir_hash,
      '--manifest',
      provenance.manifest_hash,
      '--catalog',
      provenance.catalog_hash,
    ],
    { input: traceData },
  );
  assert.equal(validate.status, 0, validate.stderr);
  const validationSummary = JSON.parse(validate.stdout.trim());
  assert.equal(validationSummary.ok, true);
  assert.equal(validationSummary.meta_checked, true);
  assert.equal(validationSummary.invalid, 0);
  assert.equal(validationSummary.total, traceLines.length);

  const verify = runNode(
    cliPath,
    [
      '--ir',
      irPath,
      '--trace',
      tempTracePath,
      '--status',
      tempStatusPath,
      '--manifest',
      manifestPath,
      '--catalog',
      specCatalogPath,
    ],
  );
  assert.equal(verify.status, 0, verify.stderr);
  const verifyResult = JSON.parse(verify.stdout.trim());
  assert.equal(verifyResult.ok, true);
  assert.equal(verifyResult.counts.provenance_mismatches, 0);

  const badVerify = runNode(
    cliPath,
    [
      '--ir',
      irPath,
      '--trace',
      tempTracePath,
      '--status',
      tempStatusPath,
      '--manifest',
      manifestPath,
      '--manifest-hash',
      'sha256:deadbeef',
      '--catalog',
      specCatalogPath,
    ],
  );
  assert.equal(badVerify.status, 1);
  const badResult = JSON.parse(badVerify.stdout.trim());
  assert.equal(badResult.ok, false);
  assert.ok(badResult.issues.some((issue) => issue.includes('manifest_hash expected sha256:deadbeef')));
  assert.ok(badResult.counts.provenance_mismatches > 0);

});
