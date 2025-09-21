#!/usr/bin/env node
import './pilot-min.mjs';
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { copyFileSync } from 'node:fs';
import { dirname, isAbsolute, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { summariseFile } from '../packages/pilot-core/dist/index.js';
import { canonicalStringify, hashJsonLike } from './hash-jsonl.mjs';
import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const FIXED_TS = process.env.TF_FIXED_TS || '1750000000000';
const baseEnv = { ...process.env, TF_FIXED_TS: String(FIXED_TS) };

function resolveOutDir() {
  const override = process.env.PILOT_FULL_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-full');
}

const outDir = resolveOutDir();
const codegenDir = join(outDir, 'codegen-ts', 'pilot_full');
const specCatalogPath = join(rootDir, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');
const tfCompose = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const tfManifest = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const traceSummary = join(rootDir, 'packages', 'tf-l0-tools', 'trace-summary.mjs');
const flowPath = join(rootDir, 'examples', 'flows', 'pilot_full.tf');

function sh(cmd, args, options = {}) {
  const env = options.env ? { ...baseEnv, ...options.env } : baseEnv;
  const result = spawnSync(cmd, args, { stdio: 'inherit', ...options, env });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

async function ensureDirs() {
  await mkdir(outDir, { recursive: true });
  await mkdir(codegenDir, { recursive: true });
}

async function removeIfExists(path) {
  await rm(path, { recursive: true, force: true });
}

function rewriteFootprints(list) {
  if (!Array.isArray(list)) return [];
  return list.map((entry) => {
    if (!entry || typeof entry !== 'object') return entry;
    if (typeof entry.uri === 'string' && entry.uri.startsWith('res://kv/')) {
      return { ...entry, uri: entry.uri.replace('res://kv/', 'res://pilot-full/') };
    }
    return entry;
  });
}

async function rewriteManifest(path) {
  const manifestRaw = await readFile(path, 'utf8');
  const manifest = JSON.parse(manifestRaw);
  manifest.footprints = rewriteFootprints(manifest.footprints);
  if (manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes)) {
    manifest.footprints_rw = {
      ...manifest.footprints_rw,
      writes: rewriteFootprints(manifest.footprints_rw.writes),
    };
  }
  await writeFile(path, JSON.stringify(manifest, null, 2) + '\n');
  return manifest;
}

async function patchRunFile(runPath, manifest, manifestHash, irHash) {
  let source = await readFile(runPath, 'utf8');
  if (manifest) {
    const manifestPattern = /const MANIFEST = [^;]*?;\n/;
    source = source.replace(manifestPattern, `const MANIFEST = ${JSON.stringify(manifest)};\n`);
  }
  if (typeof manifestHash === 'string') {
    const manifestHashPattern = /const MANIFEST_HASH = '[^']*';/;
    source = source.replace(manifestHashPattern, `const MANIFEST_HASH = '${manifestHash}';`);
  }
  if (typeof irHash === 'string') {
    const irHashPattern = /const IR_HASH = '[^']*';/;
    source = source.replace(irHashPattern, `const IR_HASH = '${irHash}';`);
  }
  const importPattern = /import inmem from '\.\/runtime\/inmem\.mjs';/;
  if (importPattern.test(source)) {
    source = source.replace(
      importPattern,
      "import inmem from '../../../../../scripts/lib/pilot-full-runtime.mjs';",
    );
  }
  await writeFile(runPath, source);
}

function createDeterministicClock(epochMs = FIXED_TS, stepMs = 1) {
  const origin = BigInt(epochMs);
  let current = origin * 1_000_000n;
  const step = BigInt(stepMs) * 1_000_000n;
  return {
    nowNs() {
      const value = current;
      current += step;
      return value;
    },
  };
}

async function runGeneratedRunner(genDir, capsPath, statusPath, tracePath) {
  const prevStatus = process.env.TF_STATUS_PATH;
  const prevTrace = process.env.TF_TRACE_PATH;
  const prevFixedTs = process.env.TF_FIXED_TS;
  const prevPilotOut = process.env.PILOT_FULL_OUT_DIR;
  const prevArgv = process.argv;
  const prevClock = globalThis.__tf_clock;

  process.env.TF_STATUS_PATH = statusPath;
  process.env.TF_TRACE_PATH = tracePath;
  process.env.TF_FIXED_TS = String(FIXED_TS);
  process.env.PILOT_FULL_OUT_DIR = outDir;
  globalThis.__tf_clock = createDeterministicClock(FIXED_TS);
  process.argv = [process.argv[0], join(genDir, 'run.mjs'), '--caps', capsPath];

  try {
    await import(pathToFileURL(join(genDir, 'run.mjs')).href);
  } finally {
    if (prevStatus === undefined) delete process.env.TF_STATUS_PATH;
    else process.env.TF_STATUS_PATH = prevStatus;
    if (prevTrace === undefined) delete process.env.TF_TRACE_PATH;
    else process.env.TF_TRACE_PATH = prevTrace;
    if (prevFixedTs === undefined) delete process.env.TF_FIXED_TS;
    else process.env.TF_FIXED_TS = prevFixedTs;
    if (prevPilotOut === undefined) delete process.env.PILOT_FULL_OUT_DIR;
    else process.env.PILOT_FULL_OUT_DIR = prevPilotOut;
    process.argv = prevArgv;
    if (prevClock === undefined) delete globalThis.__tf_clock;
    else globalThis.__tf_clock = prevClock;
  }
  if (process.exitCode && process.exitCode !== 0) {
    const code = process.exitCode;
    process.exitCode = 0;
    process.exit(code);
  }
}

async function main() {
  await ensureDirs();

  const irPath = join(outDir, 'pilot_full.ir.json');
  const canonPath = join(outDir, 'pilot_full.canon.json');
  const manifestPath = join(outDir, 'pilot_full.manifest.json');

  sh('node', [tfCompose, 'parse', flowPath, '-o', irPath]);
  sh('node', [tfCompose, 'canon', flowPath, '-o', canonPath]);
  sh('node', [tfManifest, flowPath, '-o', manifestPath]);

  const manifest = await rewriteManifest(manifestPath);

  await mkdir(codegenDir, { recursive: true });
  sh('node', [tfCompose, 'emit', '--lang', 'ts', flowPath, '--out', codegenDir]);

  const irRaw = await readFile(irPath, 'utf8');
  const irHash = sha256OfCanonicalJson(JSON.parse(irRaw));
  const manifestHash = await hashJsonLike(manifestPath);

  await patchRunFile(join(codegenDir, 'run.mjs'), manifest, manifestHash, irHash);

  const caps = {
    effects: ['Network.Out', 'Storage.Read', 'Storage.Write', 'Observability', 'Pure'],
    allow_writes_prefixes: ['res://pilot-full/'],
  };
  const capsPath = join(codegenDir, 'caps.json');
  await writeFile(capsPath, JSON.stringify(caps, null, 2) + '\n');

  await writeFile(join(outDir, 'catalog.json'), await readFile(specCatalogPath, 'utf8'));

  const statusPath = join(outDir, 'status.json');
  const tracePath = join(outDir, 'trace.jsonl');
  const summaryPath = join(outDir, 'summary.json');
  const digestsPath = join(outDir, 'digests.json');

  await removeIfExists(statusPath);
  await removeIfExists(tracePath);
  await removeIfExists(summaryPath);
  await removeIfExists(digestsPath);

  const framesPath = join(outDir, 'frames.ndjson');
  const ordersPath = join(outDir, 'orders.ndjson');
  const metricsPath = join(outDir, 'metrics.ndjson');
  const fillsPath = join(outDir, 'fills.ndjson');
  const statePath = join(outDir, 'state.json');

  await Promise.all([
    removeIfExists(framesPath),
    removeIfExists(ordersPath),
    removeIfExists(metricsPath),
    removeIfExists(fillsPath),
    removeIfExists(statePath),
  ]);

  await runGeneratedRunner(codegenDir, capsPath, statusPath, tracePath);

  const traceRaw = await readFile(tracePath, 'utf8');
  if (!traceRaw.trim()) {
    throw new Error('pilot-full-build-run: empty trace output');
  }
  const status = JSON.parse(await readFile(statusPath, 'utf8'));
  if (status.ok !== true) throw new Error('pilot-full-build-run: status.ok must be true');
  if (!Number.isFinite(status.ops) || status.ops < 5) {
    throw new Error('pilot-full-build-run: unexpected ops count');
  }
  if (!Array.isArray(status.effects) || !status.effects.includes('Network.Out')) {
    throw new Error('pilot-full-build-run: status missing Network.Out effect');
  }
  status.manifest_path = manifestPath;
  await writeFile(statusPath, JSON.stringify(status, null, 2) + '\n');

  const summaryProc = spawnSync('node', [traceSummary], {
    input: traceRaw,
    encoding: 'utf8',
    env: baseEnv,
  });
  if (summaryProc.status !== 0) {
    throw new Error('pilot-full-build-run: trace-summary failed');
  }
  const traceSummaryJson = JSON.parse(summaryProc.stdout);

  const artifactsSummary = {
    frames: summariseFile(framesPath),
    orders: summariseFile(ordersPath),
    fills: summariseFile(fillsPath),
    metrics: summariseFile(metricsPath),
    state: summariseFile(statePath),
  };

  const summaryPayload = {
    trace: traceSummaryJson,
    artifacts: artifactsSummary,
  };
  await writeFile(summaryPath, canonicalStringify(summaryPayload) + '\n');

  const digests = {
    status: await hashJsonLike(statusPath),
    trace: await hashJsonLike(tracePath),
    summary: await hashJsonLike(summaryPath),
    frames: await hashJsonLike(framesPath),
    orders: await hashJsonLike(ordersPath),
    fills: await hashJsonLike(fillsPath),
    metrics: await hashJsonLike(metricsPath),
    state: await hashJsonLike(statePath),
    ir: await hashJsonLike(irPath),
    canon: await hashJsonLike(canonPath),
    manifest: await hashJsonLike(manifestPath),
  };
  await writeFile(digestsPath, JSON.stringify(digests, null, 2) + '\n');

  copyFileSync(statusPath, join(outDir, 'status.latest.json'));
  copyFileSync(tracePath, join(outDir, 'trace.latest.jsonl'));
  copyFileSync(summaryPath, join(outDir, 'summary.latest.json'));

  console.log('pilot-full-build-run: completed artifacts in', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
