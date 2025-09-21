import test from 'node:test';
import { strict as assert } from 'node:assert';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const tfCli = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const tfManifestCli = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const pilotFlow = join(repoRoot, 'examples', 'flows', 'pilot_min.tf');
const validateCli = join(repoRoot, 'scripts', 'validate-trace.mjs');
const verifyCli = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf-verify-trace.mjs');

const expectedCaps = ['Network.Out', 'Storage.Write', 'Observability', 'Pure'];

function runNode(scriptPath, args, options = {}) {
  const result = spawnSync(process.execPath, [scriptPath, ...args], {
    cwd: repoRoot,
    stdio: 'inherit',
    ...options,
  });
  if (result.status !== 0) {
    throw new Error(`command failed: ${scriptPath} ${args.join(' ')}`);
  }
  return result;
}

function rewriteFootprints(list, ledgerUri) {
  if (!Array.isArray(list)) return [];
  return list.map((entry) => {
    if (!entry || typeof entry !== 'object') return entry;
    if (typeof entry.uri === 'string' && entry.uri.startsWith('res://kv/')) {
      const updated = { ...entry, uri: ledgerUri };
      if (updated.notes === 'seed') updated.notes = 'pilot ledger write';
      return updated;
    }
    return entry;
  });
}

function rewriteManifestFile(manifestPath, ledgerUri) {
  const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));
  manifest.footprints = rewriteFootprints(manifest.footprints, ledgerUri);
  if (manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes)) {
    manifest.footprints_rw = {
      ...manifest.footprints_rw,
      writes: rewriteFootprints(manifest.footprints_rw.writes, ledgerUri),
    };
  }
  writeFileSync(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`);
  return manifest;
}

function patchRunManifest(runPath, manifest) {
  const source = readFileSync(runPath, 'utf8');
  const marker = 'const MANIFEST = ';
  const idx = source.indexOf(marker);
  if (idx === -1) return;
  const start = idx + marker.length;
  const remainder = source.slice(start);
  const end = remainder.indexOf(';\n');
  if (end === -1) return;
  const prefix = source.slice(0, start);
  const suffix = remainder.slice(end + 2);
  const next = `${prefix}${JSON.stringify(manifest)};\n${suffix}`;
  writeFileSync(runPath, next);
}

test('pilot provenance surfaced in status and trace', { concurrency: false }, () => {
  const tmpRoot = mkdtempSync(join(tmpdir(), 'tf-provenance-'));
  const ledgerUri = 'res://ledger/pilot';
  try {
    const irPath = join(tmpRoot, 'pilot_min.ir.json');
    const manifestPath = join(tmpRoot, 'pilot_min.manifest.json');
    const codegenDir = join(tmpRoot, 'codegen');
    const statusPath = join(tmpRoot, 'status.json');
    const tracePath = join(tmpRoot, 'trace.jsonl');

    runNode(tfCli, ['parse', pilotFlow, '-o', irPath]);
    runNode(tfManifestCli, [pilotFlow, '-o', manifestPath]);
    const manifest = rewriteManifestFile(manifestPath, ledgerUri);
    runNode(tfCli, ['emit', '--lang', 'ts', pilotFlow, '--out', codegenDir]);
    patchRunManifest(join(codegenDir, 'run.mjs'), manifest);

    const capsPath = join(codegenDir, 'caps.json');
    writeFileSync(
      capsPath,
      `${JSON.stringify({
        effects: expectedCaps,
        allow_writes_prefixes: ['res://ledger/'],
      })}\n`,
    );

    const runResult = spawnSync(
      process.execPath,
      [join(codegenDir, 'run.mjs'), '--caps', capsPath],
      {
        cwd: repoRoot,
        env: {
          ...process.env,
          TF_STATUS_PATH: statusPath,
          TF_TRACE_PATH: tracePath,
          TF_PROVENANCE: '1',
        },
        encoding: 'utf8',
      },
    );
    assert.equal(runResult.status, 0, runResult.stderr);

    const status = JSON.parse(readFileSync(statusPath, 'utf8'));
    assert.equal(status.ok, true);
    assert.ok(Array.isArray(status.effects));
    assert.ok(status.effects.includes('Network.Out'));
    assert.ok(status.effects.some((effect) => effect.startsWith('Observability')));
    assert.ok(status.effects.includes('Storage.Write'));

    const provenance = status.provenance;
    assert.ok(provenance && typeof provenance === 'object');
    assert.equal(typeof provenance.ir_hash, 'string');
    assert.equal(typeof provenance.manifest_hash, 'string');
    assert.equal(typeof provenance.catalog_hash, 'string');
    assert.equal(typeof provenance.caps_source, 'string');
    assert.ok(Array.isArray(provenance.caps_effects));
    for (const effect of expectedCaps) {
      assert.ok(provenance.caps_effects.includes(effect), `caps effects missing ${effect}`);
    }

    const traceRaw = readFileSync(tracePath, 'utf8');
    const validate = spawnSync(
      process.execPath,
      [
        validateCli,
        '--require-meta',
        '--ir',
        provenance.ir_hash,
        '--manifest',
        provenance.manifest_hash,
        '--catalog',
        provenance.catalog_hash,
      ],
      { cwd: repoRoot, input: traceRaw, encoding: 'utf8' },
    );
    assert.equal(validate.status, 0, validate.stderr);
    const validateSummary = JSON.parse(validate.stdout.trim());
    assert.equal(validateSummary.ok, true);
    assert.equal(validateSummary.invalid, 0);
    assert.equal(validateSummary.meta_checked, true);

    const verify = spawnSync(
      process.execPath,
      [
        verifyCli,
        '--ir',
        irPath,
        '--trace',
        tracePath,
        '--status',
        statusPath,
        '--manifest',
        manifestPath,
        '--catalog',
        join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json'),
      ],
      { cwd: repoRoot, encoding: 'utf8' },
    );
    assert.equal(verify.status, 0, verify.stderr);
    const verifyResult = JSON.parse(verify.stdout.trim());
    assert.equal(verifyResult.ok, true);
    assert.equal(verifyResult.counts.provenance_mismatches, 0);

    const verifyBad = spawnSync(
      process.execPath,
      [
        verifyCli,
        '--ir',
        irPath,
        '--trace',
        tracePath,
        '--status',
        statusPath,
        '--manifest',
        manifestPath,
        '--manifest-hash',
        'sha256:deadbeef',
        '--catalog',
        join(repoRoot, 'packages', 'tf-l0-spec', 'spec', 'catalog.json'),
      ],
      { cwd: repoRoot, encoding: 'utf8' },
    );
    assert.notEqual(verifyBad.status, 0);
    const verifyBadResult = JSON.parse(verifyBad.stdout.trim());
    assert.equal(verifyBadResult.ok, false);
    assert.ok(verifyBadResult.issues.some((issue) => issue.includes('manifest_hash')));
    assert.ok(verifyBadResult.counts.provenance_mismatches > 0);
  } finally {
    rmSync(tmpRoot, { recursive: true, force: true });
  }
});
