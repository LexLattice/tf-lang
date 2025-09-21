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

function extractSummary(output) {
  const lines = output.split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    try {
      return JSON.parse(lines[i]);
    } catch {}
  }
  throw new Error(`unable to locate JSON summary in output: ${output}`);
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
  const okSummary = extractSummary(allowed.stdout);
  assert.equal(okSummary.ok, true);
  assert.equal(okSummary.ops, 2);
  assert.deepEqual(okSummary.effects, ['Storage.Write']);
  assert.ok(okSummary.provenance);
  assert.equal(okSummary.provenance.caps_source, 'file');
  assert.deepEqual(okSummary.provenance.caps_effects, ['Observability', 'Pure', 'Storage.Write']);
  assert.match(okSummary.provenance.ir_hash, /^sha256:/);
  assert.match(okSummary.provenance.manifest_hash, /^sha256:/);
  assert.match(okSummary.provenance.catalog_hash, /^sha256:/);

  const denied = await runProcess(process.execPath, [runScript]);
  assert.equal(denied.code, 1);
  const deniedSummary = extractSummary(denied.stdout);
  assert.equal(deniedSummary.ok, false);
  assert.match(denied.stderr, /no capabilities provided/i);
  assert.ok(!deniedSummary.provenance);
});

test('runner accepts env capabilities and file takes precedence', async () => {
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

  const envOnly = await runProcess(process.execPath, [runScript], {
    env: { TF_CAPS: JSON.stringify({ effects: ['Network.Out', 'Pure'], allow_writes_prefixes: [] }) },
  });
  assert.equal(envOnly.code, 0, envOnly.stderr);
  const envSummary = extractSummary(envOnly.stdout);
  assert.equal(envSummary.ok, true);
  assert.equal(envSummary.ops, 1);
  assert.deepEqual(envSummary.effects, ['Network.Out']);
  assert.ok(envSummary.provenance);
  assert.equal(envSummary.provenance.caps_source, 'env');
  assert.deepEqual(envSummary.provenance.caps_effects, ['Network.Out', 'Pure']);

  const fileBeatsEnv = await runProcess(
    process.execPath,
    [runScript, '--caps', capsPath],
    {
      env: { TF_CAPS: JSON.stringify({ effects: [], allow_writes_prefixes: [] }) },
    },
  );
  assert.equal(fileBeatsEnv.code, 0, fileBeatsEnv.stderr);
  const precedenceSummary = extractSummary(fileBeatsEnv.stdout);
  assert.equal(precedenceSummary.ok, true);
  assert.equal(precedenceSummary.ops, 1);
  assert.deepEqual(precedenceSummary.effects, ['Network.Out']);
  assert.ok(precedenceSummary.provenance);
  assert.equal(precedenceSummary.provenance.caps_source, 'file');
  assert.deepEqual(precedenceSummary.provenance.caps_effects, ['Network.Out', 'Observability', 'Pure']);
});
