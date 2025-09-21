import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { promises as fs } from 'node:fs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const tfCli = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const validatorScript = join(repoRoot, 'scripts', 'validate-trace.mjs');
const runOutDir = join(repoRoot, 'out', '0.4', 'codegen-ts', 'run_publish');
const traceDir = join(repoRoot, 'out', '0.4', 'traces');
const tracePath = join(traceDir, 'publish.jsonl');

function runNode(args, { cwd = repoRoot, env, input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, args, {
      cwd,
      env: { ...process.env, ...env },
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

test('trace writer emits JSONL and validator enforces schema', async () => {
  await fs.mkdir(traceDir, { recursive: true });

  const emit = await runNode([
    tfCli,
    'emit',
    '--lang',
    'ts',
    join('examples', 'flows', 'run_publish.tf'),
    '--out',
    runOutDir,
  ]);
  assert.equal(emit.code, 0, emit.stderr);

  const capsPath = join(traceDir, 'caps.json');
  const caps = {
    effects: ['Network.Out', 'Pure', 'Observability'],
    allow_writes_prefixes: [],
  };
  await fs.writeFile(capsPath, JSON.stringify(caps));
  await fs.rm(tracePath, { force: true });

  const runnerPath = join(runOutDir, 'run.mjs');
  const run = await runNode([runnerPath, '--caps', capsPath], {
    env: { TF_TRACE_PATH: tracePath },
  });
  assert.equal(run.code, 0, run.stderr);

  const traceContent = await fs.readFile(tracePath, 'utf8');
  const traceLines = traceContent
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
  assert.ok(traceLines.length >= 1, 'expected at least one trace line');

  const valid = await runNode([validatorScript], { input: traceContent });
  assert.equal(valid.code, 0, valid.stderr);
  const validSummary = JSON.parse(valid.stdout.trim());
  assert.equal(validSummary.ok, true);
  assert.equal(validSummary.invalid, 0);
  assert.ok(validSummary.total >= 1);

  const invalidContent = '{"ts":1,"args":{},"region":"","effect":""}\n';
  const invalid = await runNode([validatorScript], { input: invalidContent });
  assert.equal(invalid.code, 1, invalid.stderr);
  const invalidSummary = JSON.parse(invalid.stdout.trim());
  assert.equal(invalidSummary.ok, false);
  assert.equal(invalidSummary.invalid, 1);
  assert.ok(Array.isArray(invalidSummary.examples));
  assert.ok(invalidSummary.examples.length >= 1);
  assert.equal(invalidSummary.examples[0].error, 'prim_id is required');
});
