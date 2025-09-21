import { test } from 'node:test';
import { strict as assert } from 'node:assert';
import { spawn } from 'node:child_process';
import { promises as fs } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';
import path from 'node:path';

const tfCliPath = fileURLToPath(new URL('../packages/tf-compose/bin/tf.mjs', import.meta.url));
const flowPath = fileURLToPath(new URL('../examples/flows/run_publish.tf', import.meta.url));
const runOutDir = fileURLToPath(new URL('../out/0.4/codegen-ts/run_publish', import.meta.url));
const runnerPath = path.join(runOutDir, 'run.mjs');
const tracesDir = fileURLToPath(new URL('../out/0.4/traces', import.meta.url));
const tracePath = path.join(tracesDir, 'publish.jsonl');
const validatorPath = fileURLToPath(new URL('../scripts/validate-trace.mjs', import.meta.url));

function runNode(args, { input, env } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, args, {
      stdio: ['pipe', 'pipe', 'pipe'],
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

    if (input !== undefined) {
      child.stdin.end(input);
    } else {
      child.stdin.end();
    }
  });
}

test('trace writer emits JSONL and validator enforces schema', async () => {
  await fs.mkdir(path.dirname(runOutDir), { recursive: true });
  await fs.mkdir(tracesDir, { recursive: true });
  await fs.rm(runOutDir, { recursive: true, force: true });
  await fs.rm(tracePath, { force: true });

  const emitResult = await runNode([tfCliPath, 'emit', '--lang', 'ts', flowPath, '--out', runOutDir]);
  assert.equal(emitResult.code, 0, emitResult.stderr);

  const capsPath = '/tmp/caps2.json';
  await fs.writeFile(
    capsPath,
    JSON.stringify({ effects: ['Network.Out', 'Pure', 'Observability'], allow_writes_prefixes: [] })
  );

  const runResult = await runNode(
    [runnerPath, '--caps', capsPath],
    { env: { TF_TRACE_PATH: tracePath } }
  );
  assert.equal(runResult.code, 0, runResult.stderr);
  assert.ok(runResult.stdout.includes('prim_id'), 'expected stdout to include trace output');

  const traceData = await fs.readFile(tracePath, 'utf8');
  const traceLines = traceData.split('\n').filter((line) => line.trim().length > 0);
  assert.ok(traceLines.length >= 1, 'expected at least one trace line');

  const validResult = await runNode([validatorPath], { input: traceData });
  assert.equal(validResult.code, 0, validResult.stderr);
  const validSummary = JSON.parse(validResult.stdout.trim());
  assert.equal(validSummary.ok, true);
  assert.equal(validSummary.invalid, 0);
  assert.ok(validSummary.total >= 1);

  const tempDir = await fs.mkdtemp(path.join(tmpdir(), 'tf-trace-'));
  const badTracePath = path.join(tempDir, 'bad.jsonl');
  await fs.writeFile(badTracePath, '{"ts":1,"args":{},"region":"","effect":"Pure"}\n');
  const badInput = await fs.readFile(badTracePath, 'utf8');
  const invalidResult = await runNode([validatorPath], { input: badInput });
  assert.equal(invalidResult.code, 1, invalidResult.stderr);
  const invalidSummary = JSON.parse(invalidResult.stdout.trim());
  assert.equal(invalidSummary.ok, false);
  assert.equal(invalidSummary.total, 1);
  assert.equal(invalidSummary.invalid, 1);
  assert.ok(Array.isArray(invalidSummary.examples));
  assert.ok(invalidSummary.examples.length >= 1);
  assert.equal(invalidSummary.examples[0].line, 1);
  assert.equal(invalidSummary.examples[0].error, 'prim_id is required');
});
