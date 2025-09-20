import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { mkdtemp, readFile, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const tfCli = fileURLToPath(new URL('../packages/tf-compose/bin/tf.mjs', import.meta.url));
const storageFlow = fileURLToPath(new URL('../examples/flows/run_storage_ok.tf', import.meta.url));
const publishFlow = fileURLToPath(new URL('../examples/flows/run_publish.tf', import.meta.url));

async function runProcess(bin, args, { cwd, env, input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(bin, args, {
      cwd,
      env: env ? { ...process.env, ...env } : process.env,
      stdio: ['pipe', 'pipe', 'pipe'],
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

function parseSummary(output) {
  const lines = output.trim().split(/\r?\n/).filter(Boolean);
  const last = lines[lines.length - 1] || '{}';
  return JSON.parse(last);
}

async function emitFlow(flowPath) {
  const tmp = await mkdtemp(join(tmpdir(), 'tf-runner-'));
  const outDir = join(tmp, 'out');
  const result = await runProcess(process.execPath, [tfCli, 'emit', flowPath, '--lang', 'ts', '--out', outDir]);
  assert.equal(result.code, 0, result.stderr);
  return { outDir, runScript: join(outDir, 'run.mjs') };
}

test('generated runner embeds manifest constant', async () => {
  const { runScript } = await emitFlow(storageFlow);
  const contents = await readFile(runScript, 'utf8');
  assert.match(contents, /const MANIFEST = \{/);
  assert.match(contents, /required_effects/);
});

test('runner enforces capability requirements for storage flow', async () => {
  const { outDir, runScript } = await emitFlow(storageFlow);
  const capsPath = join(outDir, 'caps.json');
  await writeFile(
    capsPath,
    JSON.stringify({
      effects: ['Storage.Write', 'Pure', 'Observability'],
      allow_writes_prefixes: ['res://kv/'],
    }),
    'utf8',
  );

  const allowed = await runProcess(process.execPath, [runScript, '--caps', capsPath]);
  assert.equal(allowed.code, 0, allowed.stderr);
  const okSummary = parseSummary(allowed.stdout);
  assert.equal(okSummary.ok, true);
  assert.ok(okSummary.effects.includes('Storage.Write'));

  const denied = await runProcess(process.execPath, [runScript]);
  assert.equal(denied.code, 0);
  const deniedSummary = parseSummary(denied.stdout);
  assert.equal(deniedSummary.ok, false);
  assert.match(denied.stderr, /(missing_effects|write_denied)/);
});

test('runner permits publish flow with matching caps', async () => {
  const { outDir, runScript } = await emitFlow(publishFlow);
  const capsPath = join(outDir, 'caps.json');
  await writeFile(
    capsPath,
    JSON.stringify({
      effects: ['Network.Out', 'Pure', 'Observability'],
      allow_writes_prefixes: [],
    }),
    'utf8',
  );

  const result = await runProcess(process.execPath, [runScript, '--caps', capsPath]);
  assert.equal(result.code, 0, result.stderr);
  const summary = parseSummary(result.stdout);
  assert.equal(summary.ok, true);
  assert.ok(summary.effects.includes('Network.Out'));
});
