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

function runScript({ env } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [scriptPath], {
      cwd: repoRoot,
      stdio: ['ignore', 'pipe', 'pipe'],
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
  });
}

async function readJson(path) {
  return JSON.parse(await readFile(path, 'utf8'));
}

test('app-order publish script is deterministic and resilient', async () => {
  const first = await runScript();
  assert.equal(first.code, 0, first.stderr);

  await access(statusPath, fsConstants.F_OK);
  await access(summaryPath, fsConstants.F_OK);

  const status = await readJson(statusPath);
  assert.equal(status.ok, true, 'expected ok status');
  assert.ok(status.ops >= 1, 'expected at least one operation recorded');
  assert.ok(
    Array.isArray(status.effects) && status.effects.includes('Network.Out'),
    'expected Network.Out effect in status',
  );

  const summaryRaw = await readFile(summaryPath, 'utf8');
  const summary = JSON.parse(summaryRaw);
  assert.ok(summary.total >= 1, 'expected at least one trace event');
  assert.ok(
    summary.by_prim && typeof summary.by_prim['tf:network/publish@1'] === 'number',
    'expected publish primitive count',
  );
  assert.ok(
    summary.by_effect && typeof summary.by_effect['Network.Out'] === 'number',
    'expected Network.Out effect count',
  );

  const second = await runScript();
  assert.equal(second.code, 0, second.stderr);
  const summarySecondRaw = await readFile(summaryPath, 'utf8');
  assert.equal(summaryRaw, summarySecondRaw, 'expected identical summaries across runs');

  const fallback = await runScript({
    env: { APP_ORDER_PUBLISH_DISABLE_TRACE_FILE: '1' },
  });
  assert.equal(fallback.code, 0, fallback.stderr);
  const fallbackSummary = await readJson(summaryPath);
  assert.ok(
    fallbackSummary.by_effect && typeof fallbackSummary.by_effect['Network.Out'] === 'number',
    'expected Network.Out effect in fallback summary',
  );
  assert.ok(
    fallbackSummary.total >= 1,
    'expected fallback summary to include at least one event',
  );
});
