import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { access, readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const scriptPath = fileURLToPath(new URL('../scripts/app-order-publish.mjs', import.meta.url));
const statusPath = fileURLToPath(new URL('../out/0.4/apps/order_publish/status.json', import.meta.url));
const summaryPath = fileURLToPath(new URL('../out/0.4/apps/order_publish/summary.json', import.meta.url));

async function runScript() {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [scriptPath], {
      stdio: ['ignore', 'pipe', 'pipe'],
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

test('app-order-publish script emits and summarizes order publish flow', async () => {
  const result = await runScript();
  assert.equal(result.code, 0, result.stderr);

  await access(statusPath);
  await access(summaryPath);

  const rawSummary = await readFile(summaryPath, 'utf8');
  const summary = JSON.parse(rawSummary);

  assert.ok(summary.total >= 1, 'expected total events >= 1');
  assert.ok(summary.by_prim?.['tf:network/publish@1'] >= 1, 'expected publish primitive count');
  assert.ok(summary.by_effect?.['Network.Out'] >= 1, 'expected Network.Out effect count');
});
