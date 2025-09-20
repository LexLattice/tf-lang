import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);

async function emitFlow(flowPath) {
  const base = await mkdtemp(join(tmpdir(), 'tf-runner-'));
  await execFileAsync('node', [
    'packages/tf-compose/bin/tf.mjs',
    'emit',
    flowPath,
    '--lang',
    'ts',
    '--out',
    base,
  ]);
  return {
    dir: base,
    runScript: join(base, 'run.mjs'),
  };
}

async function runNode(scriptPath, args = [], options = {}) {
  try {
    return await execFileAsync('node', [scriptPath, ...args], options);
  } catch (error) {
    if (error && typeof error === 'object' && 'stdout' in error) {
      return {
        stdout: error.stdout ?? '',
        stderr: error.stderr ?? '',
        code: error.code ?? 1,
      };
    }
    throw error;
  }
}

function parseSummary(stdout) {
  const lines = String(stdout)
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
  assert(lines.length > 0, 'expected summary output');
  const last = lines[lines.length - 1];
  return JSON.parse(last);
}

const storageCaps = {
  effects: ['Storage.Write', 'Pure', 'Observability'],
  allow_writes_prefixes: ['res://kv/'],
};

const publishCaps = {
  effects: ['Network.Out', 'Pure', 'Observability'],
  allow_writes_prefixes: [],
};

test('generated runner accepts sufficient capabilities', async () => {
  const { runScript, dir } = await emitFlow('examples/flows/run_storage_ok.tf');
  const capsPath = join(dir, 'caps.json');
  await writeFile(capsPath, JSON.stringify(storageCaps), 'utf8');
  const { stdout } = await runNode(runScript, ['--caps', capsPath]);
  const summary = parseSummary(stdout);
  assert.equal(summary.ok, true);
  assert.equal(summary.ops > 0, true);
  assert(summary.effects.includes('Storage.Write'));
});

test('generated runner rejects insufficient capabilities', async () => {
  const { runScript, dir } = await emitFlow('examples/flows/run_publish.tf');
  const capsPath = join(dir, 'caps-deny.json');
  await writeFile(
    capsPath,
    JSON.stringify({ effects: [], allow_writes_prefixes: [] }),
    'utf8'
  );
  const { stdout, stderr } = await runNode(runScript, ['--caps', capsPath]);
  const summary = parseSummary(stdout);
  assert.equal(summary.ok, false);
  assert.match(stderr, /missing_effects|write_denied/);
});

test('generated runner accepts publish capabilities', async () => {
  const { runScript, dir } = await emitFlow('examples/flows/run_publish.tf');
  const capsPath = join(dir, 'caps-ok.json');
  await writeFile(capsPath, JSON.stringify(publishCaps), 'utf8');
  const { stdout } = await runNode(runScript, ['--caps', capsPath]);
  const summary = parseSummary(stdout);
  assert.equal(summary.ok, true);
  assert(summary.effects.includes('Network.Out'));
});
