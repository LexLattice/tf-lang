import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = dirname(__dirname);

async function runCommand(cmd, args, options = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(cmd, args, {
      cwd: repoRoot,
      stdio: ['ignore', 'pipe', 'pipe'],
      ...options
    });
    const stdoutChunks = [];
    const stderrChunks = [];
    child.stdout.on('data', (chunk) => stdoutChunks.push(chunk));
    child.stderr.on('data', (chunk) => stderrChunks.push(chunk));
    child.on('error', reject);
    child.on('close', (code) => {
      resolve({
        code,
        stdout: Buffer.concat(stdoutChunks).toString('utf8'),
        stderr: Buffer.concat(stderrChunks).toString('utf8')
      });
    });
  });
}

function parseLastJson(stdout = '') {
  const lines = stdout
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean);
  if (lines.length === 0) {
    throw new Error('expected JSON output, got empty stdout');
  }
  return JSON.parse(lines[lines.length - 1]);
}

async function generateFlow(flowPath) {
  const outDir = await mkdtemp(join(tmpdir(), 'tf-runner-'));
  const args = [
    'packages/tf-compose/bin/tf.mjs',
    'emit',
    flowPath,
    '--lang',
    'ts',
    '--out',
    outDir
  ];
  const result = await runCommand('node', args);
  assert.strictEqual(result.code, 0, `generation failed: ${result.stderr}`);
  return outDir;
}

test('generated runner embeds manifest and enforces capabilities', async () => {
  const outDir = await generateFlow('examples/flows/run_storage_ok.tf');
  const runSource = await readFile(join(outDir, 'run.mjs'), 'utf8');
  assert.ok(runSource.includes('const MANIFEST = {'), 'manifest literal missing');

  const capsPath = join(outDir, 'caps.json');
  await writeFile(
    capsPath,
    JSON.stringify(
      {
        effects: ['Storage.Write', 'Pure', 'Observability'],
        allow_writes_prefixes: ['res://kv/']
      },
      null,
      2
    )
  );

  const okRun = await runCommand('node', [join(outDir, 'run.mjs'), '--caps', capsPath]);
  assert.strictEqual(okRun.code, 0, `runner exited non-zero: ${okRun.stderr}`);
  const parsedOk = parseLastJson(okRun.stdout);
  assert.equal(parsedOk.ok, true);
  assert.ok(parsedOk.effects.includes('Storage.Write'));

  const deniedRun = await runCommand('node', [join(outDir, 'run.mjs')]);
  assert.equal(parseLastJson(deniedRun.stdout).ok, false);
  assert.ok(/missing_effects|write_denied/.test(deniedRun.stderr));
});

test('publish flow requires network capability', async () => {
  const outDir = await generateFlow('examples/flows/run_publish.tf');
  const capsPath = join(outDir, 'caps.json');
  await writeFile(
    capsPath,
    JSON.stringify(
      {
        effects: ['Network.Out', 'Pure', 'Observability'],
        allow_writes_prefixes: []
      },
      null,
      2
    )
  );

  const okRun = await runCommand('node', [join(outDir, 'run.mjs'), '--caps', capsPath]);
  assert.strictEqual(okRun.code, 0, `runner exited non-zero: ${okRun.stderr}`);
  const parsed = parseLastJson(okRun.stdout);
  assert.equal(parsed.ok, true);
  assert.ok(parsed.effects.includes('Network.Out'));
});
