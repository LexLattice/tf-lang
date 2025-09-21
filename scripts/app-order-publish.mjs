import { spawn } from 'node:child_process';
import { access, mkdir, readFile, rm, stat, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const repoRoot = fileURLToPath(new URL('..', import.meta.url));
const tfCli = join(repoRoot, 'packages/tf-compose/bin/tf.mjs');
const flowPath = join(repoRoot, 'examples/flows/app_order_publish.tf');
const outDir = join(repoRoot, 'out/0.4/apps/order_publish');
const runScriptPath = join(outDir, 'run.mjs');
const statusPath = join(outDir, 'status.json');
const tracePath = join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');
const capsPath = '/tmp/caps.order.json';
const traceSummaryCli = join(repoRoot, 'packages/tf-l0-tools/trace-summary.mjs');

function runProcess(command, args, { cwd = repoRoot, env = process.env, input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, {
      cwd,
      env,
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

function ensureNonEmpty(content, fallbackName) {
  if (content && content.trim().length > 0) {
    return content;
  }
  throw new Error(`No trace data captured from ${fallbackName}`);
}

await rm(outDir, { recursive: true, force: true });
await mkdir(outDir, { recursive: true });

const emitResult = await runProcess(process.execPath, [tfCli, 'emit', '--lang', 'ts', flowPath, '--out', outDir]);
if (emitResult.code !== 0) {
  throw new Error(`tf emit failed: ${emitResult.stderr || emitResult.stdout}`);
}

await writeFile(
  capsPath,
  `${JSON.stringify({ effects: ['Network.Out', 'Observability', 'Pure'], allow_writes_prefixes: [] })}\n`,
);

const runEnv = {
  ...process.env,
  TF_STATUS_PATH: statusPath,
  TF_TRACE_PATH: tracePath,
};

const runResult = await runProcess(process.execPath, [runScriptPath, '--caps', capsPath], { env: runEnv });
if (runResult.code !== 0) {
  throw new Error(`run.mjs failed: ${runResult.stderr || runResult.stdout}`);
}

let traceData = '';
let traceSource = 'stdout';
try {
  await access(tracePath);
  const stats = await stat(tracePath);
  if (stats.size > 0) {
    traceData = await readFile(tracePath, 'utf8');
    traceSource = tracePath;
  }
} catch {}

if (!traceData) {
  traceData = ensureNonEmpty(runResult.stdout, 'run.mjs stdout');
}

const statusJson = await readFile(statusPath, 'utf8');
const status = JSON.parse(statusJson);
let augmentedTrace = traceData;
if (Array.isArray(status.effects) && status.effects.length > 0) {
  const effectLines = status.effects.map((effect) => JSON.stringify({ effect }));
  augmentedTrace = `${traceData.trimEnd()}\n${effectLines.join('\n')}\n`;
}

const summaryResult = await runProcess(process.execPath, [traceSummaryCli, '--pretty'], { input: augmentedTrace });
if (summaryResult.code !== 0) {
  throw new Error(`trace-summary failed: ${summaryResult.stderr || summaryResult.stdout}`);
}

await writeFile(summaryPath, summaryResult.stdout);

console.log(`status: ${statusPath} summary: ${summaryPath}`);
if (traceSource === tracePath) {
  console.log(`trace captured at ${tracePath}`);
}
