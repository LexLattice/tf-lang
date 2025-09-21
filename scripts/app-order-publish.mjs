#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { join, relative } from 'node:path';

const repoRoot = fileURLToPath(new URL('..', import.meta.url));
const tfCli = fileURLToPath(new URL('../packages/tf-compose/bin/tf.mjs', import.meta.url));
const traceSummaryCli = fileURLToPath(new URL('../packages/tf-l0-tools/trace-summary.mjs', import.meta.url));
const flowPath = fileURLToPath(new URL('../examples/flows/app_order_publish.tf', import.meta.url));
const outDir = fileURLToPath(new URL('../out/0.4/apps/order_publish', import.meta.url));
const runScriptPath = join(outDir, 'run.mjs');
const statusPath = join(outDir, 'status.json');
const tracePath = join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');
const capsPath = '/tmp/caps.order.json';

function fail(message, stderr) {
  if (stderr) process.stderr.write(stderr);
  console.error(message);
  process.exit(1);
}

function ensureEmit() {
  rmSync(outDir, { recursive: true, force: true });
  const emitArgs = [
    tfCli,
    'emit',
    '--lang',
    'ts',
    flowPath,
    '--out',
    outDir,
  ];
  const result = spawnSync(process.execPath, emitArgs, { stdio: 'inherit' });
  if (result.status !== 0) {
    const code = result.status ?? 1;
    process.exit(code);
  }
  if (!existsSync(runScriptPath)) {
    fail(`expected runner at ${runScriptPath}`);
  }
}

function writeCaps() {
  const caps = {
    effects: ['Network.Out', 'Observability', 'Pure'],
    allow_writes_prefixes: [],
  };
  writeFileSync(capsPath, JSON.stringify(caps), 'utf8');
}

function extractEffects(output) {
  const effects = [];
  const lines = output.split(/\r?\n/);
  for (const raw of lines) {
    const line = raw.trim();
    if (!line) continue;
    try {
      const parsed = JSON.parse(line);
      if (Array.isArray(parsed.effects)) {
        for (const effect of parsed.effects) {
          if (typeof effect === 'string') {
            effects.push(effect);
          }
        }
      }
    } catch {
      // ignore non-JSON lines
    }
  }
  return effects;
}

function runApp() {
  const env = {
    ...process.env,
    TF_STATUS_PATH: statusPath,
    TF_TRACE_PATH: tracePath,
  };
  const result = spawnSync(process.execPath, [runScriptPath, '--caps', capsPath], {
    env,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (result.stdout) {
    process.stdout.write(result.stdout);
  }
  if (result.stderr) {
    process.stderr.write(result.stderr);
  }
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
  const stdout = result.stdout ?? '';
  return { stdout, effects: extractEffects(stdout) };
}

function summarize(traceSource, extraEffects) {
  let traceInput = traceSource;
  if (existsSync(tracePath)) {
    traceInput = readFileSync(tracePath, 'utf8');
  } else if (extraEffects.length > 0) {
    const append = extraEffects.map((effect) => JSON.stringify({ effect }));
    traceInput = [traceInput.trimEnd(), ...append].filter(Boolean).join('\n');
    if (traceInput) {
      traceInput += '\n';
    }
  }
  const summary = spawnSync(process.execPath, [traceSummaryCli, '--pretty'], {
    input: traceInput,
    encoding: 'utf8',
  });
  if (summary.status !== 0) {
    fail('failed to summarize trace', summary.stderr);
  }
  mkdirSync(outDir, { recursive: true });
  writeFileSync(summaryPath, summary.stdout, 'utf8');
}

function main() {
  ensureEmit();
  writeCaps();
  const { stdout, effects } = runApp();
  summarize(stdout, effects);
  const statusRel = relative(repoRoot, statusPath);
  const summaryRel = relative(repoRoot, summaryPath);
  console.log(`status=${statusRel} summary=${summaryRel}`);
}

main();
