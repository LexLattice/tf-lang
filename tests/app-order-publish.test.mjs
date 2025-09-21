import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { access, readFile } from 'node:fs/promises';
import { constants as fsConstants } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const scriptPath = join(repoRoot, 'scripts', 'app-order-publish.mjs');
const outDir = join(repoRoot, 'out', '0.4', 'apps', 'order_publish');
const statusPath = join(outDir, 'status.json');
const summaryPath = join(outDir, 'summary.json');

function runScript() {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [scriptPath], {
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

test('app-order publish script emits code, runs, and summarizes trace', async () => {
  const result = await runScript();
  assert.equal(result.code, 0, result.stderr);

  await access(statusPath, fsConstants.F_OK);
  await access(summaryPath, fsConstants.F_OK);

  const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
  assert.ok(summary.total >= 1, 'expected at least one trace event');
  assert.ok(
    summary.by_prim && typeof summary.by_prim['tf:network/publish@1'] === 'number',
    'expected publish primitive count',
  );
  assert.ok(
    summary.by_effect && typeof summary.by_effect['Network.Out'] === 'number',
    'expected Network.Out effect count',
  );
});
