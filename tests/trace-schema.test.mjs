import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { promises as fs } from 'node:fs';
import path from 'node:path';
import os from 'node:os';

const repoRoot = fileURLToPath(new URL('..', import.meta.url));
const tfCli = fileURLToPath(new URL('../packages/tf-compose/bin/tf.mjs', import.meta.url));
const validatorCli = fileURLToPath(new URL('../scripts/validate-trace.mjs', import.meta.url));
const publishOutDir = fileURLToPath(new URL('../out/0.4/codegen-ts/run_publish', import.meta.url));
const runScript = path.join(publishOutDir, 'run.mjs');
const tracePath = fileURLToPath(new URL('../out/0.4/traces/publish.jsonl', import.meta.url));

function runNode(args, { input, env, cwd } = {}) {
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
  await fs.rm(publishOutDir, { recursive: true, force: true });
  await fs.rm(tracePath, { force: true });
  await fs.mkdir(path.dirname(tracePath), { recursive: true });

  const emitResult = await runNode([
    tfCli,
    'emit',
    '--lang',
    'ts',
    fileURLToPath(new URL('../examples/flows/run_publish.tf', import.meta.url)),
    '--out',
    publishOutDir,
  ]);
  assert.equal(emitResult.code, 0, emitResult.stderr);

  const capsPath = path.join(os.tmpdir(), `tf-trace-caps-${process.pid}.json`);
  await fs.writeFile(
    capsPath,
    JSON.stringify({ effects: ['Network.Out', 'Pure', 'Observability'], allow_writes_prefixes: [] }),
    'utf8',
  );

  const runResult = await runNode([runScript, '--caps', capsPath], {
    env: { TF_TRACE_PATH: tracePath },
  });
  assert.equal(runResult.code, 0, runResult.stderr);

  const traceContent = await fs.readFile(tracePath, 'utf8');
  const records = traceContent
    .trim()
    .split('\n')
    .filter((line) => line);
  assert.ok(records.length >= 1, 'expected at least one trace record');

  const validResult = await runNode([validatorCli], {
    input: traceContent,
    cwd: repoRoot,
  });
  assert.equal(validResult.code, 0, validResult.stderr);
  const summary = JSON.parse(validResult.stdout.trim());
  assert.deepEqual(summary, { ok: true, total: records.length, invalid: 0 });

  const invalidLine = `${JSON.stringify({ ts: Date.now(), args: {}, effect: 'Storage.Write', region: '' })}\n`;
  const invalidResult = await runNode([validatorCli], {
    input: invalidLine,
    cwd: repoRoot,
  });
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
