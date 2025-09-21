import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { promises as fs } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const tfCli = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const validatorCli = join(repoRoot, 'scripts', 'validate-trace.mjs');
const publishOutDir = join(repoRoot, 'out', '0.4', 'codegen-ts', 'run_publish');
const tracesDir = join(repoRoot, 'out', '0.4', 'traces');
const tracePath = join(tracesDir, 'publish.jsonl');
const runIrSourceUrl = pathToFileURL(
  join(repoRoot, 'packages', 'tf-l0-codegen-ts', 'src', 'runtime', 'run-ir.mjs'),
).href;

function runNode(script, args = [], { cwd = repoRoot, env = {}, input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [script, ...args], {
      cwd,
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

test('trace writer emits JSONL and validator flags issues', async () => {
  await fs.rm(publishOutDir, { recursive: true, force: true }).catch(() => {});
  await fs.rm(tracePath, { force: true }).catch(() => {});
  await fs.mkdir(tracesDir, { recursive: true });

  const emitResult = await runNode(tfCli, [
    'emit',
    '--lang',
    'ts',
    'examples/flows/run_publish.tf',
    '--out',
    publishOutDir,
  ]);
  assert.equal(emitResult.code, 0, emitResult.stderr);

  const tempDir = await fs.mkdtemp(join(tmpdir(), 'tf-caps-'));
  const capsPath = join(tempDir, 'caps.json');
  await fs.writeFile(
    capsPath,
    JSON.stringify({ effects: ['Network.Out', 'Pure', 'Observability'], allow_writes_prefixes: [] }),
  );

  const runResult = await runNode(join(publishOutDir, 'run.mjs'), ['--caps', capsPath], {
    env: { TF_TRACE_PATH: tracePath },
  });
  assert.equal(runResult.code, 0, runResult.stderr);

  const traceRaw = await fs.readFile(tracePath, 'utf8');
  const traceLines = traceRaw.split('\n').filter((line) => line.trim() !== '');
  assert.ok(traceLines.length >= 1, 'expected at least one trace line written');

  const beforeMultiCount = traceLines.length;
  const multiRunScript = `import { runIR } from '${runIrSourceUrl}';
const runtime = {
  ping: async () => ({ ok: true }),
  effects: { ping: 'Pure' },
};
const ir = { node: 'Seq', children: [{ node: 'Prim', prim: 'ping', args: {} }] };
await runIR(ir, runtime);
await runIR(ir, runtime);
`;
  const multiScriptPath = join(tempDir, 'multi-run.mjs');
  await fs.writeFile(multiScriptPath, multiRunScript, 'utf8');
  const multiResult = await runNode(multiScriptPath, [], {
    env: { TF_TRACE_PATH: tracePath },
  });
  assert.equal(multiResult.code, 0, multiResult.stderr);
  const afterMultiRaw = await fs.readFile(tracePath, 'utf8');
  const afterMultiLines = afterMultiRaw.split('\n').filter((line) => line.trim() !== '');
  assert.ok(
    afterMultiLines.length >= beforeMultiCount + 2,
    `expected at least two new trace lines after multi-run append (before=${beforeMultiCount}, after=${afterMultiLines.length})`,
  );

  const finalTraceRaw = afterMultiRaw;
  const finalTraceLines = afterMultiLines;

  const validateOk = await runNode(validatorCli, [], { input: finalTraceRaw });
  assert.equal(validateOk.code, 0, validateOk.stderr);
  const okSummary = JSON.parse(validateOk.stdout.trim());
  assert.equal(okSummary.ok, true, 'expected validator ok summary');
  assert.equal(okSummary.invalid, 0);
  assert.equal(okSummary.total, finalTraceLines.length);

  const unwritableEnv = { TF_TRACE_PATH: '/root/nope/publish.jsonl' };
  const unwritableResult = await runNode(join(publishOutDir, 'run.mjs'), ['--caps', capsPath], {
    env: unwritableEnv,
  });
  assert.equal(unwritableResult.code, 0, unwritableResult.stderr);
  const stdoutLines = unwritableResult.stdout
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line !== '');
  const traceLineOnStdout = stdoutLines.find((line) => {
    try {
      const parsed = JSON.parse(line);
      return parsed && typeof parsed.prim_id === 'string';
    } catch {
      return false;
    }
  });
  assert.ok(traceLineOnStdout, 'expected a trace JSON object on stdout when file is unwritable');

  const badLine = JSON.stringify({ ts: 0, args: {} }) + '\n';
  const validateBad = await runNode(validatorCli, [], { input: badLine });
  assert.equal(validateBad.code, 1, validateBad.stderr);
  const badSummary = JSON.parse(validateBad.stdout.trim());
  assert.equal(badSummary.ok, false, 'expected validator to fail');
  assert.equal(badSummary.invalid, 1);
  assert.ok(Array.isArray(badSummary.examples) && badSummary.examples.length >= 1);
  assert.equal(badSummary.examples[0].line, 1);
  assert.ok(/prim_id/.test(badSummary.examples[0].error));
});
