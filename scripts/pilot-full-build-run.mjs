#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile, rm } from 'node:fs/promises';
import { copyFileSync } from 'node:fs';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { canonicalStringify, hashJsonLike } from './hash-jsonl.mjs';
import { toNdjson, toJson } from './lib/pilot-full-support.mjs';
import { extractPilotOutputs } from './lib/pilot-full-runtime.mjs';
import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');
const FIXED_TS = process.env.TF_FIXED_TS || '1750000000000';
const baseEnv = { ...process.env, TF_FIXED_TS: String(FIXED_TS) };

const tfCompose = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const tfManifest = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const traceSummary = join(rootDir, 'packages', 'tf-l0-tools', 'trace-summary.mjs');
const flowPath = join(rootDir, 'examples', 'flows', 'pilot_full.tf');
const specCatalogPath = join(rootDir, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');

function resolveOutDir() {
  const override = process.env.PILOT_FULL_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-full');
}

const outDir = resolveOutDir();
const codegenDir = join(outDir, 'codegen-ts', 'pilot_full');

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

function rewriteManifest(manifestPath) {
  return readFile(manifestPath, 'utf8').then((raw) => {
    const manifest = JSON.parse(raw);
    const effects = ['Storage.Read', 'Storage.Write', 'Network.Out', 'Observability', 'Pure'];
    manifest.effects = effects;
    manifest.required_effects = effects;
    const writes = [
      { mode: 'write', uri: 'res://pilot-full/frames', notes: 'pilot full frames' },
      { mode: 'write', uri: 'res://pilot-full/orders', notes: 'pilot full orders' },
      { mode: 'write', uri: 'res://pilot-full/fills', notes: 'pilot full fills' },
      { mode: 'write', uri: 'res://pilot-full/state', notes: 'pilot full state' },
    ];
    manifest.footprints = writes;
    manifest.footprints_rw = { reads: [], writes };
    return writeFile(manifestPath, JSON.stringify(manifest, null, 2) + '\n').then(() => manifest);
  });
}

async function patchRunFile(runPath, manifest, manifestHash, irHash) {
  let source = await readFile(runPath, 'utf8');
  source = source.replace(
    "import inmem from './runtime/inmem.mjs';",
    "import { createPilotFullRuntime } from '../../../../../scripts/lib/pilot-full-runtime.mjs';\nconst inmem = createPilotFullRuntime();\nexport const RUNTIME = inmem;",
  );
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
  const prevArgv = process.argv;
  const prevClock = globalThis.__tf_clock;

  process.env.TF_STATUS_PATH = statusPath;
  process.env.TF_TRACE_PATH = tracePath;
  process.env.TF_FIXED_TS = String(FIXED_TS);
  globalThis.__tf_clock = createDeterministicClock(FIXED_TS);
  process.argv = [process.argv[0], join(genDir, 'run.mjs'), '--caps', capsPath];

  try {
    const mod = await import(pathToFileURL(join(genDir, 'run.mjs')).href);
    if (process.exitCode && process.exitCode !== 0) {
      const code = process.exitCode;
      process.exitCode = 0;
      process.exit(code);
    }
    return mod;
  } finally {
    if (prevStatus === undefined) delete process.env.TF_STATUS_PATH;
    else process.env.TF_STATUS_PATH = prevStatus;
    if (prevTrace === undefined) delete process.env.TF_TRACE_PATH;
    else process.env.TF_TRACE_PATH = prevTrace;
    if (prevFixedTs === undefined) delete process.env.TF_FIXED_TS;
    else process.env.TF_FIXED_TS = prevFixedTs;
    process.argv = prevArgv;
    if (prevClock === undefined) delete globalThis.__tf_clock;
    else globalThis.__tf_clock = prevClock;
  }
}

async function main() {
  await ensureDirs();

  const irPath = join(outDir, 'pilot_full.ir.json');
  const canonPath = join(outDir, 'pilot_full.canon.json');
  const manifestPath = join(outDir, 'pilot_full.manifest.json');
  const statusPath = join(outDir, 'status.json');
  const tracePath = join(outDir, 'trace.jsonl');
  const summaryPath = join(outDir, 'summary.json');
  const framesPath = join(outDir, 'frames.ndjson');
  const ordersPath = join(outDir, 'orders.ndjson');
  const fillsPath = join(outDir, 'fills.ndjson');
  const statePath = join(outDir, 'state.json');
  const catalogPath = join(outDir, 'catalog.json');

  await removeIfExists(codegenDir);
  await removeIfExists(statusPath);
  await removeIfExists(tracePath);
  await removeIfExists(summaryPath);
  await removeIfExists(framesPath);
  await removeIfExists(ordersPath);
  await removeIfExists(fillsPath);
  await removeIfExists(statePath);

  await mkdir(codegenDir, { recursive: true });

  sh('node', [tfCompose, 'parse', flowPath, '-o', irPath]);
  sh('node', [tfCompose, 'canon', flowPath, '-o', canonPath]);
  sh('node', [tfManifest, flowPath, '-o', manifestPath]);

  const manifest = await rewriteManifest(manifestPath);
  const irRaw = await readFile(irPath, 'utf8');
  const irHash = sha256OfCanonicalJson(JSON.parse(irRaw));
  const manifestHash = sha256OfCanonicalJson(manifest);

  sh('node', [tfCompose, 'emit', '--lang', 'ts', flowPath, '--out', codegenDir]);
  await writeFile(join(codegenDir, 'caps.json'), JSON.stringify({
    effects: ['Storage.Read', 'Storage.Write', 'Network.Out', 'Observability', 'Pure'],
    allow_writes_prefixes: ['res://pilot-full/'],
  }, null, 2) + '\n');

  await writeFile(catalogPath, await readFile(specCatalogPath, 'utf8'));

  await patchRunFile(join(codegenDir, 'run.mjs'), manifest, manifestHash, irHash);

  const mod = await runGeneratedRunner(codegenDir, join(codegenDir, 'caps.json'), statusPath, tracePath);
  const runtime = mod?.RUNTIME;
  const outputs = extractPilotOutputs(runtime) ?? {};

  if (outputs.frames) {
    await writeFile(framesPath, toNdjson(outputs.frames));
  }
  if (outputs.orders) {
    await writeFile(ordersPath, toNdjson(outputs.orders));
  }
  if (outputs.fills) {
    await writeFile(fillsPath, toNdjson(outputs.fills));
  }
  if (outputs.state) {
    await writeFile(statePath, toJson(outputs.state));
  }

  const traceRaw = await readFile(tracePath, 'utf8');
  if (!traceRaw.trim()) {
    throw new Error('pilot-full-build-run: empty trace output');
  }
  const status = JSON.parse(await readFile(statusPath, 'utf8'));
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
  const summaryJson = JSON.parse(summaryProc.stdout);
  const canonicalSummary = canonicalStringify(summaryJson);
  await writeFile(summaryPath, canonicalSummary + '\n');

  const digests = {
    status: await hashJsonLike(statusPath),
    trace: await hashJsonLike(tracePath),
    summary: await hashJsonLike(summaryPath),
    frames: await hashJsonLike(framesPath),
    orders: await hashJsonLike(ordersPath),
    fills: await hashJsonLike(fillsPath),
    state: await hashJsonLike(statePath),
    ir: await hashJsonLike(irPath),
    canon: await hashJsonLike(canonPath),
    manifest: await hashJsonLike(manifestPath),
    catalog: await hashJsonLike(catalogPath),
  };

  await writeFile(join(outDir, 'digests.json'), JSON.stringify(digests, null, 2) + '\n');

  copyFileSync(statusPath, join(codegenDir, 'status.json'));

  console.log('pilot-full-build-run: completed artifacts in', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
