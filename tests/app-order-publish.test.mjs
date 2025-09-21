import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { promises as fs } from 'node:fs';

const ROOT = resolve(dirname(fileURLToPath(new URL(import.meta.url))), '..');
const SCRIPT_PATH = resolve(ROOT, 'scripts/app-order-publish.mjs');
const STATUS_PATH = resolve(ROOT, 'out/0.4/apps/order_publish/status.json');
const SUMMARY_PATH = resolve(ROOT, 'out/0.4/apps/order_publish/summary.json');

function runScript() {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [SCRIPT_PATH], {
      cwd: ROOT,
      stdio: ['inherit', 'pipe', 'pipe']
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
  });
}

test('app-order-publish script emits artifacts and trace summary', async () => {
  const result = await runScript();
  assert.equal(result.code, 0, result.stderr || result.stdout);

  await fs.access(STATUS_PATH);
  await fs.access(SUMMARY_PATH);

  const rawSummary = await fs.readFile(SUMMARY_PATH, 'utf8');
  const summary = JSON.parse(rawSummary);

  assert.ok(summary.total >= 1, 'expected at least one trace event');
  assert.ok(
    summary?.by_prim?.['tf:network/publish@1'] >= 1,
    'expected tf:network/publish@1 in trace summary'
  );
  assert.ok(
    summary?.by_effect?.['Network.Out'] >= 1,
    'expected Network.Out effect count in trace summary'
  );
});
