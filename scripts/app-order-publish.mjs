#!/usr/bin/env node
import { spawn } from 'node:child_process';
import { access, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { constants as fsConstants } from 'node:fs';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = dirname(fileURLToPath(new URL(import.meta.url)));
const ROOT = resolve(__dirname, '..');
const FLOW_PATH = resolve(ROOT, 'examples/flows/app_order_publish.tf');
const OUT_DIR = resolve(ROOT, 'out/0.4/apps/order_publish');
const CAPS_PATH = '/tmp/caps.order.json';
const STATUS_PATH = resolve(OUT_DIR, 'status.json');
const TRACE_PATH = resolve(OUT_DIR, 'trace.jsonl');
const SUMMARY_PATH = resolve(OUT_DIR, 'summary.json');
const TF_CLI = resolve(ROOT, 'packages/tf-compose/bin/tf.mjs');
const TRACE_SUMMARY_CLI = resolve(ROOT, 'packages/tf-l0-tools/trace-summary.mjs');

const CAPS = {
  effects: ['Network.Out', 'Observability', 'Pure'],
  allow_writes_prefixes: []
};

async function main() {
  await mkdir(OUT_DIR, { recursive: true });
  await rm(STATUS_PATH, { force: true });
  await rm(TRACE_PATH, { force: true });
  await rm(SUMMARY_PATH, { force: true });

  await runCommand(process.execPath, [TF_CLI, 'emit', '--lang', 'ts', FLOW_PATH, '--out', OUT_DIR]);

  await writeFile(CAPS_PATH, JSON.stringify(CAPS), 'utf8');

  const runEnv = { ...process.env, TF_STATUS_PATH: STATUS_PATH, TF_TRACE_PATH: TRACE_PATH };
  const runScriptPath = resolve(OUT_DIR, 'run.mjs');
  const { stdout: runStdout } = await runCommand(
    process.execPath,
    [runScriptPath, '--caps', CAPS_PATH],
    { env: runEnv, captureStdout: true }
  );

  const traceSource = await selectTraceSource(runStdout);
  const enrichedTrace = await enrichTrace(traceSource);
  const { stdout: summary } = await runCommand(
    process.execPath,
    [TRACE_SUMMARY_CLI, '--pretty'],
    { captureStdout: true, input: enrichedTrace }
  );

  await writeFile(SUMMARY_PATH, summary, 'utf8');

  process.stdout.write(`status=${STATUS_PATH} summary=${SUMMARY_PATH}\n`);
}

async function selectTraceSource(runStdout) {
  if (await fileExists(TRACE_PATH)) {
    return readFile(TRACE_PATH, 'utf8');
  }
  if (runStdout && runStdout.trim().length > 0) {
    return runStdout;
  }
  throw new Error('No trace output produced by generated runner');
}

async function enrichTrace(rawTrace) {
  if (!rawTrace) {
    return rawTrace;
  }

  const lines = rawTrace
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);

  if (lines.length === 0) {
    return rawTrace;
  }

  const effectResolver = await loadEffectResolver();
  if (!effectResolver) {
    return lines.join('\n') + '\n';
  }

  const rewritten = lines.map((line) => {
    try {
      const parsed = JSON.parse(line);
      if (parsed && parsed.prim_id && !parsed.effect) {
        const effect = effectResolver(parsed.prim_id);
        if (effect) {
          parsed.effect = effect;
        }
      }
      return JSON.stringify(parsed);
    } catch {
      return line;
    }
  });

  return rewritten.join('\n') + '\n';
}

async function loadEffectResolver() {
  const runtimeUrl = pathToFileURL(resolve(OUT_DIR, 'runtime/inmem.mjs'));
  try {
    const runtimeModule = await import(runtimeUrl.href);
    const candidate = runtimeModule?.default ?? runtimeModule;
    if (candidate && typeof candidate.effectFor === 'function') {
      return (prim) => candidate.effectFor(prim);
    }
    if (typeof runtimeModule?.effectFor === 'function') {
      return (prim) => runtimeModule.effectFor(prim);
    }
  } catch (err) {
    process.stderr.write(`warn: unable to load runtime for effect mapping (${err?.message ?? err})\n`);
  }
  return null;
}

function runCommand(cmd, args, { env = process.env, captureStdout = false, input } = {}) {
  return new Promise((resolve, reject) => {
    const stdio = [input !== undefined ? 'pipe' : 'inherit', captureStdout ? 'pipe' : 'inherit', 'inherit'];
    const child = spawn(cmd, args, {
      cwd: ROOT,
      env,
      stdio
    });

    let stdout = '';

    if (captureStdout && child.stdout) {
      child.stdout.setEncoding('utf8');
      child.stdout.on('data', (chunk) => {
        stdout += chunk;
      });
    }

    child.on('error', reject);
    child.on('close', (code) => {
      if (code !== 0) {
        const error = new Error(`${cmd} ${args.join(' ')} exited with code ${code}`);
        error.code = code;
        error.stdout = stdout;
        reject(error);
        return;
      }
      resolve({ stdout });
    });

    if (input !== undefined && child.stdin) {
      child.stdin.end(input);
    }
  });
}

async function fileExists(path) {
  try {
    await access(path, fsConstants.F_OK);
    return true;
  } catch {
    return false;
  }
}

main().catch((err) => {
  process.stderr.write(String(err?.stack || err));
  process.stderr.write('\n');
  process.exit(1);
});
