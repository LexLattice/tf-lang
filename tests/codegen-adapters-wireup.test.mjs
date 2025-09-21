import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync, rmSync, existsSync, mkdirSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.join(__dirname, '..');
const cliPath = path.join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const validatorCli = path.join(repoRoot, 'scripts', 'validate-trace.mjs');
const outRoot = path.join(repoRoot, 'out', '0.4', 'codegen-ts');
const capsPath = path.join(repoRoot, 'tests', 'fixtures', 'caps-observability.json');

const FLOWS = [
  {
    name: 'storage_cas',
    flow: path.join(repoRoot, 'examples', 'flows', 'storage_cas.tf'),
    expectedEffects: ['Storage.Read', 'Storage.Write'],
  },
  {
    name: 'crypto_sign_verify',
    flow: path.join(repoRoot, 'examples', 'flows', 'crypto_sign_verify.tf'),
    expectedEffects: ['Crypto'],
  },
  {
    name: 'metrics_publish',
    flow: path.join(repoRoot, 'examples', 'flows', 'metrics_publish.tf'),
    expectedEffects: ['Network.Out', 'Observability.EmitMetric'],
  },
];

function emitFlow(flowPath, outDir) {
  rmSync(outDir, { recursive: true, force: true });
  const result = spawnSync(process.execPath, [
    cliPath,
    'emit',
    '--lang',
    'ts',
    flowPath,
    '--out',
    outDir,
  ], {
    cwd: repoRoot,
    encoding: 'utf8',
  });
  assert.equal(result.status, 0, result.stderr || result.stdout);
  assert.ok(existsSync(path.join(outDir, 'run.mjs')), 'run.mjs should exist after emit');
}

function runPipeline(outDir, extraEnv = {}) {
  const env = { ...process.env, ...extraEnv };
  const runPath = path.join(outDir, 'run.mjs');
  const result = spawnSync(process.execPath, [runPath, '--caps', capsPath], {
    cwd: outDir,
    encoding: 'utf8',
    env,
  });
  assert.equal(result.status, 0, result.stderr);
  const lines = result.stdout
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
  let summaryRaw = null;
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    try {
      const candidate = JSON.parse(lines[i]);
      if (candidate && typeof candidate.ok === 'boolean' && Array.isArray(candidate.effects)) {
        summaryRaw = lines[i];
        break;
      }
    } catch {
      continue;
    }
  }
  assert.ok(summaryRaw, 'summary json should be present on stdout');
  const summary = JSON.parse(summaryRaw);
  const statusPath = path.join(outDir, 'status.json');
  const statusRaw = readFileSync(statusPath, 'utf8');
  return { summary, summaryRaw, statusRaw };
}

test('generated TS runners wire adapters and remain deterministic', () => {
  mkdirSync(outRoot, { recursive: true });

  for (const spec of FLOWS) {
    const outDir = path.join(outRoot, spec.name);
    emitFlow(spec.flow, outDir);

    const tracePath = path.join(outDir, 'trace.jsonl');
    const traceRun = runPipeline(outDir, { TF_TRACE_PATH: tracePath });
    assert.equal(traceRun.summary.ok, true, `expected ok run for ${spec.name}`);

    if (existsSync(tracePath)) {
      const traceContents = readFileSync(tracePath, 'utf8');
      if (traceContents.trim().length > 0) {
        const validate = spawnSync(process.execPath, [validatorCli], {
          cwd: repoRoot,
          encoding: 'utf8',
          input: traceContents,
        });
        assert.equal(validate.status, 0, validate.stderr);
        const validatorSummary = JSON.parse(validate.stdout.trim());
        assert.equal(validatorSummary.ok, true, 'trace validator should accept trace');
      }
    }

    const first = runPipeline(outDir);
    const second = runPipeline(outDir);

    assert.equal(first.summary.ok, true, `${spec.name} summary should be ok`);
    assert.ok(first.summary.ops >= 1, `${spec.name} should execute at least one operation`);
    for (const effect of spec.expectedEffects) {
      assert.ok(
        first.summary.effects.includes(effect),
        `${spec.name} should include ${effect} in effects (${first.summary.effects.join(', ')})`,
      );
    }

    assert.equal(first.summaryRaw, second.summaryRaw, `${spec.name} stdout summary should be stable`);
    assert.equal(first.statusRaw, second.statusRaw, `${spec.name} status.json should be deterministic`);
  }
});
