import test from 'node:test';
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { rm, readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const execFileAsync = promisify(execFile);

const repoRoot = fileURLToPath(new URL('..', import.meta.url));
const capsPath = join(repoRoot, 'tests/fixtures/caps-all.json');
const flows = [
  {
    name: 'storage_cas',
    flowPath: join(repoRoot, 'examples/flows/storage_cas.tf'),
    expectEffects: ['Storage.Write'],
  },
  {
    name: 'crypto_sign_verify',
    flowPath: join(repoRoot, 'examples/flows/crypto_sign_verify.tf'),
    expectEffects: ['Crypto'],
  },
  {
    name: 'metrics_publish',
    flowPath: join(repoRoot, 'examples/flows/metrics_publish.tf'),
    expectEffects: ['Network.Out', 'Observability.EmitMetric'],
  },
];

async function runFlow(outDir) {
  const runScript = join(outDir, 'run.mjs');
  const { stdout } = await execFileAsync('node', [runScript, '--caps', capsPath], { cwd: outDir });
  const lastLine = stdout.trim().split('\n').filter(Boolean).pop();
  return JSON.parse(lastLine);
}

test('generated TS pipelines wire adapters into the runtime', async (t) => {
  for (const flow of flows) {
    await t.test(flow.name, async () => {
      const outDir = join(repoRoot, 'out', '0.4', 'codegen-ts', flow.name);
      await rm(outDir, { recursive: true, force: true });
      await execFileAsync('node', [
        join(repoRoot, 'packages/tf-compose/bin/tf.mjs'),
        '--',
        'emit',
        '--lang',
        'ts',
        flow.flowPath,
        '--out',
        outDir,
      ], { cwd: repoRoot });

      const first = await runFlow(outDir);
      assert.equal(first.ok, true, 'first run ok');
      assert.ok(Number.isFinite(first.ops) && first.ops >= 1, 'first run has ops');
      for (const effect of flow.expectEffects) {
        assert.ok(first.effects.includes(effect), `expected effect ${effect}`);
      }

      const statusPath = join(outDir, 'status.json');
      const firstStatusRaw = await readFile(statusPath, 'utf8');

      const second = await runFlow(outDir);
      assert.equal(second.ok, true, 'second run ok');
      assert.deepEqual(second.effects, first.effects, 'effects deterministic');
      assert.equal(second.ops, first.ops, 'ops deterministic');
      const secondStatusRaw = await readFile(statusPath, 'utf8');
      assert.equal(secondStatusRaw, firstStatusRaw, 'status.json deterministic');
    });
  }
});
