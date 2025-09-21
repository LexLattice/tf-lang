import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { promises as fs } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const tfCli = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const validatorCli = join(repoRoot, 'scripts', 'validate-trace.mjs');

function runNode(script, args = [], { cwd = repoRoot, env = {}, input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [script, ...args], {
      cwd,
      stdio: ['pipe', 'pipe', 'pipe'],
      env: { ...process.env, ...env },
    });

    let stdout = '';
    let stderr = '';

    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', (chunk) => {
      stdout += chunk;
    });
    child.stderr.on('data', (chunk) => {
      stderr += chunk;
    });
    child.on('error', reject);
    child.on('close', (code) => {
      resolve({ code, stdout, stderr });
    });

    if (input !== undefined) {
      child.stdin.end(input);
    } else {
      child.stdin.end();
    }
  });
}

const flows = [
  {
    name: 'storage_cas',
    path: 'examples/flows/storage_cas.tf',
    expectedEffects: ['Storage.Write'],
    minOps: 3,
    caps: {
      effects: ['Storage.Write', 'Storage.Read', 'Pure'],
      allow_writes_prefixes: ['res://kv/'],
    },
  },
  {
    name: 'crypto_sign_verify',
    path: 'examples/flows/crypto_sign_verify.tf',
    expectedEffects: ['Crypto'],
    minOps: 2,
    caps: {
      effects: ['Crypto', 'Pure'],
      allow_writes_prefixes: [],
    },
  },
  {
    name: 'metrics_publish',
    path: 'examples/flows/metrics_publish.tf',
    expectedEffects: ['Network.Out', 'Observability.EmitMetric'],
    minOps: 2,
    caps: {
      effects: ['Network.Out', 'Observability.EmitMetric', 'Observability', 'Pure'],
      allow_writes_prefixes: [],
    },
  },
];

test('generated adapters run end-to-end with in-memory implementations', async () => {
  const tempRoot = await fs.mkdtemp(join(tmpdir(), 'tf-wireup-'));
  for (const flow of flows) {
    const outDir = join(repoRoot, 'out', '0.4', 'codegen-ts', flow.name);
    await fs.rm(outDir, { recursive: true, force: true }).catch(() => {});
    const emit = await runNode(tfCli, ['emit', '--lang', 'ts', flow.path, '--out', outDir]);
    assert.equal(emit.code, 0, emit.stderr);

    const capsPath = join(tempRoot, `${flow.name}-caps.json`);
    await fs.writeFile(capsPath, JSON.stringify(flow.caps));

    const tracePath = join(tempRoot, `${flow.name}-trace.jsonl`);

    const run1 = await runNode(join(outDir, 'run.mjs'), ['--caps', capsPath], { env: { TF_TRACE_PATH: tracePath } });
    assert.equal(run1.code, 0, run1.stderr);
    const summaryLine = run1.stdout.trim().split('\n').filter(Boolean).pop();
    assert.ok(summaryLine, 'expected summary JSON on stdout');
    const summary = JSON.parse(summaryLine);
    assert.equal(summary.ok, true, `expected ok summary for ${flow.name}`);
    assert.ok(summary.ops >= flow.minOps, `expected at least ${flow.minOps} ops for ${flow.name}`);
    for (const effect of flow.expectedEffects) {
      assert.ok(summary.effects.includes(effect), `expected effect ${effect} in ${flow.name}`);
    }

    const statusPath = join(outDir, 'status.json');
    const statusFirst = await fs.readFile(statusPath, 'utf8');

    const run2 = await runNode(join(outDir, 'run.mjs'), ['--caps', capsPath], { env: { TF_TRACE_PATH: tracePath } });
    assert.equal(run2.code, 0, run2.stderr);
    const summaryLineTwo = run2.stdout.trim().split('\n').filter(Boolean).pop();
    assert.equal(summaryLineTwo, summaryLine, 'summary output should be deterministic');
    const statusSecond = await fs.readFile(statusPath, 'utf8');
    assert.equal(statusSecond, statusFirst, 'status.json should be stable between runs');

    try {
      const traceRaw = await fs.readFile(tracePath, 'utf8');
      if (traceRaw.trim().length > 0) {
        const validate = await runNode(validatorCli, [], { input: traceRaw });
        assert.equal(validate.code, 0, validate.stderr);
        const validatorSummary = JSON.parse(validate.stdout.trim());
        assert.equal(validatorSummary.ok, true);
      }
    } catch (err) {
      if (err?.code !== 'ENOENT') throw err;
    }
  }
});
