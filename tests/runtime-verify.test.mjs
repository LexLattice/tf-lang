import test from 'node:test';
import { strict as assert } from 'node:assert';
import { spawnSync } from 'node:child_process';
import { readFileSync, existsSync } from 'node:fs';
import { promises as fsp } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const verifyOutPath = path.join(repoRoot, 'out/0.4/verify/test/report.json');

function withPilotEnv(pilotOutDir, extra = {}) {
  return {
    ...process.env,
    TF_PROVENANCE: '1',
    TF_FIXED_TS: '1750000000000',
    PILOT_OUT_DIR: pilotOutDir,
    ...extra,
  };
}

function runPilotBuild(pilotOutDir) {
  return spawnSync(process.execPath, ['scripts/pilot-build-run.mjs'], {
    cwd: repoRoot,
    env: withPilotEnv(pilotOutDir),
    stdio: 'pipe',
    encoding: 'utf8',
  });
}

function runRuntimeVerify(pilotOutDir, args = []) {
  return spawnSync(process.execPath, ['scripts/runtime-verify.mjs', ...args], {
    cwd: repoRoot,
    env: withPilotEnv(pilotOutDir),
    stdio: 'pipe',
    encoding: 'utf8',
  });
}

async function makePilotOutDir() {
  const base = path.join(repoRoot, 'out/0.4/pilot-l0');
  await fsp.mkdir(base, { recursive: true });
  return fsp.mkdtemp(path.join(base, 'verify-'));
}

function mutateBufferByte(buffer) {
  const mutated = Buffer.from(buffer);
  for (let index = 0; index < mutated.length; index += 1) {
    const code = mutated[index];
    const isAlpha = (code >= 65 && code <= 90) || (code >= 97 && code <= 122);
    const isDigit = code >= 48 && code <= 57;
    if (isAlpha || isDigit) {
      mutated[index] = isDigit ? ((code - 48 + 1) % 10) + 48 : code === 122 ? 121 : code + 1;
      return mutated;
    }
  }
  if (mutated.length === 0) {
    return Buffer.from('{"corrupted":true}\n');
  }
  mutated[0] = mutated[0] === 0x7b ? 0x5b : mutated[0] ^ 0x01;
  return mutated;
}

test('runtime verify CLI produces deterministic reports and detects catalog tampering', async () => {
  const pilotOutDir = await makePilotOutDir();
  try {
    const build = runPilotBuild(pilotOutDir);
    assert.equal(build.status, 0, build.stderr);

    const catalogPath = path.join(pilotOutDir, 'catalog.json');
    assert.ok(existsSync(catalogPath), 'expected catalog.json after pilot build');

    const first = runRuntimeVerify(pilotOutDir, [
      '--flow',
      'pilot',
      '--out',
      verifyOutPath,
      '--print-inputs',
    ]);
    assert.equal(first.status, 0, first.stderr);
    const reportRaw1 = readFileSync(verifyOutPath, 'utf8');
    const report1 = JSON.parse(reportRaw1);
    assert.equal(report1.ok, true);
    assert.equal(report1.steps.validate, true);
    assert.equal(report1.steps.verify, true);
    assert.ok(report1.inputs);
    assert.equal(report1.inputs.catalog.path.endsWith('catalog.json'), true);
    assert.equal(typeof report1.inputs.catalog.sha256, 'string');
    assert.equal(typeof report1.inputs.catalog.expected, 'string');

    const status = JSON.parse(await fsp.readFile(path.join(pilotOutDir, 'status.json'), 'utf8'));
    assert.equal(report1.inputs.catalog.expected, status.provenance.catalog_hash);

    const second = runRuntimeVerify(pilotOutDir, ['--flow', 'pilot', '--out', verifyOutPath]);
    assert.equal(second.status, 0, second.stderr);
    const reportRaw2 = readFileSync(verifyOutPath, 'utf8');
    assert.equal(reportRaw2, reportRaw1);

    const originalCatalog = await fsp.readFile(catalogPath);
    try {
      const corrupted = mutateBufferByte(originalCatalog);
      await fsp.writeFile(catalogPath, corrupted);

      const failed = runRuntimeVerify(pilotOutDir, ['--flow', 'pilot', '--out', verifyOutPath]);
      assert.equal(failed.status, 3);
      const failedReport = JSON.parse(readFileSync(verifyOutPath, 'utf8'));
      assert.equal(failedReport.ok, false);
      assert.equal(failedReport.steps.validate, true);
      assert.equal(failedReport.steps.verify, false);
      assert.ok(Array.isArray(failedReport.issues));
      assert.ok(
        failedReport.issues.some((issue) => {
          if (typeof issue === 'string') return issue.includes('catalog');
          if (issue && typeof issue === 'object') return JSON.stringify(issue).includes('catalog');
          return false;
        }),
        'expected catalog-related issue',
      );
    } finally {
      await fsp.writeFile(catalogPath, originalCatalog);
    }
  } finally {
    await fsp.rm(pilotOutDir, { recursive: true, force: true });
  }
});
