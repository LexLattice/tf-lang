import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { access, readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const repoRoot = fileURLToPath(new URL('..', import.meta.url));
const scriptPath = fileURLToPath(new URL('../scripts/app-order-publish.mjs', import.meta.url));
const outDir = join(repoRoot, 'out/0.4/apps/order_publish');
const statusPath = join(outDir, 'status.json');
const summaryPath = join(outDir, 'summary.json');

function runNodeScript(path) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [path], {
      cwd: repoRoot,
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

test('app order publish script emits artifacts and summary', async () => {
  const { code, stderr } = await runNodeScript(scriptPath);
  assert.equal(code, 0, stderr);

  await access(statusPath);
  await access(summaryPath);

  const rawSummary = await readFile(summaryPath, 'utf8');
  const summary = JSON.parse(rawSummary);

  assert.ok(summary.total >= 1, 'summary.total should be >= 1');
  assert.ok(summary.by_prim?.['tf:network/publish@1'] >= 1, 'summary.by_prim should count publish');
  assert.ok(summary.by_effect?.['Network.Out'] >= 1, 'summary.by_effect should count Network.Out');
});
