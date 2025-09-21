#!/usr/bin/env node
import { mkdir, writeFile, readFile, access } from 'node:fs/promises';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const tfCli = fileURLToPath(new URL('../packages/tf-compose/bin/tf.mjs', import.meta.url));
const flowPath = fileURLToPath(new URL('../examples/flows/app_order_publish.tf', import.meta.url));
const outDir = fileURLToPath(new URL('../out/0.4/apps/order_publish', import.meta.url));
const runScript = join(outDir, 'run.mjs');
const statusPath = join(outDir, 'status.json');
const tracePath = join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');
const capsPath = '/tmp/caps.order.json';
const traceSummaryCli = fileURLToPath(new URL('../packages/tf-l0-tools/trace-summary.mjs', import.meta.url));
const runtimeModulePath = new URL('../out/0.4/apps/order_publish/runtime/inmem.mjs', import.meta.url);

async function runProcess(command, args, { cwd = here, env, input } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, {
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

await mkdir(outDir, { recursive: true });

const emitResult = await runProcess(process.execPath, [tfCli, 'emit', '--lang', 'ts', flowPath, '--out', outDir]);
if (emitResult.code !== 0) {
  console.error(emitResult.stderr || emitResult.stdout);
  process.exit(emitResult.code ?? 1);
}

const caps = {
  effects: ['Network.Out', 'Observability', 'Pure'],
  allow_writes_prefixes: [],
};
await writeFile(capsPath, JSON.stringify(caps, null, 2) + '\n', 'utf8');

const runEnv = {
  TF_STATUS_PATH: statusPath,
  TF_TRACE_PATH: tracePath,
};
const runResult = await runProcess(process.execPath, [runScript, '--caps', capsPath], { env: runEnv });
if (runResult.code !== 0) {
  console.error(runResult.stderr || runResult.stdout);
  process.exit(runResult.code ?? 1);
}

await access(statusPath);

let traceInput;
try {
  traceInput = await readFile(tracePath, 'utf8');
} catch (error) {
  if (error && error.code !== 'ENOENT') {
    throw error;
  }
  traceInput = runResult.stdout;
}

if (!traceInput || !traceInput.trim()) {
  throw new Error('no trace data produced by runner');
}

async function annotateTrace(raw) {
  const { default: runtime } = await import(runtimeModulePath);
  const effectFor = (prim) => {
    if (!prim) return null;
    if (runtime && typeof runtime.effectFor === 'function') {
      return runtime.effectFor(prim);
    }
    if (runtime?.effects && prim in runtime.effects) {
      return runtime.effects[prim];
    }
    return null;
  };
  const lines = raw.split(/\r?\n/);
  const out = [];
  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    try {
      const parsed = JSON.parse(trimmed);
      if (parsed && typeof parsed.prim_id === 'string') {
        if (parsed.effect === undefined) {
          const effect = effectFor(parsed.prim_id);
          if (effect) {
            parsed.effect = effect;
          }
        }
        out.push(JSON.stringify(parsed));
      }
    } catch (err) {
      // ignore malformed lines here; the summary tool will warn if needed
    }
  }
  return out.join('\n');
}

const annotatedTrace = (await annotateTrace(traceInput)).trimEnd();
if (!annotatedTrace) {
  throw new Error('no usable trace events produced by runner');
}

const summaryResult = await runProcess(process.execPath, [traceSummaryCli, '--pretty'], {
  input: `${annotatedTrace}\n`,
});
if (summaryResult.code !== 0) {
  console.error(summaryResult.stderr);
  process.exit(summaryResult.code ?? 1);
}

await writeFile(summaryPath, summaryResult.stdout.endsWith('\n') ? summaryResult.stdout : `${summaryResult.stdout}\n`, 'utf8');

console.log(`${statusPath} ${summaryPath}`);
