// @tf-test kind=product area=runtime speed=medium deps=node

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
      return { summary: JSON.parse(lines[i]), line: lines[i] };
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
  const { summary: okSummary, line: okLine } = extractSummary(allowed.stdout);
  const okParsed = JSON.parse(okLine);
  assert.equal(okParsed.ok, true);
  assert.equal(okParsed.ops, 2);
  assert.deepEqual(okParsed.effects, ['Storage.Write']);
  assert.ok(okParsed.provenance);
  assert.ok(okParsed.provenance.caps_effects.includes('Storage.Write'));
  assert.deepEqual(okSummary.effects, ['Storage.Write']);

  const denied = await runProcess(process.execPath, [runScript]);
  assert.equal(denied.code, 1);
  const { summary: deniedSummary, line: deniedLine } = extractSummary(denied.stdout);
  const deniedParsed = JSON.parse(deniedLine);
  assert.equal(deniedParsed.ok, false);
  assert.deepEqual(deniedParsed.effects, []);
  assert.equal(deniedSummary.ok, false);
  assert.match(denied.stderr, /no capabilities provided/i);
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
  const { summary: envSummary, line: envLine } = extractSummary(envOnly.stdout);
  const envParsed = JSON.parse(envLine);
  assert.equal(envParsed.ok, true);
  assert.deepEqual(envParsed.effects, ['Network.Out']);
  assert.equal(envParsed.provenance.caps_source, 'env');
  assert.deepEqual(envSummary.effects, ['Network.Out']);

  const fileBeatsEnv = await runProcess(
    process.execPath,
    [runScript, '--caps', capsPath],
    {
      env: { TF_CAPS: JSON.stringify({ effects: [], allow_writes_prefixes: [] }) },
    },
  );
  assert.equal(fileBeatsEnv.code, 0, fileBeatsEnv.stderr);
  const { summary: precedenceSummary, line: precedenceLine } = extractSummary(fileBeatsEnv.stdout);
  const precedenceParsed = JSON.parse(precedenceLine);
  assert.equal(precedenceParsed.ok, true);
  assert.deepEqual(precedenceParsed.effects, ['Network.Out']);
  assert.equal(precedenceParsed.provenance.caps_source, 'file');
  assert.deepEqual(precedenceSummary.effects, ['Network.Out']);
});
