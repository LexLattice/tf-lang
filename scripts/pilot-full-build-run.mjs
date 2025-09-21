#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile, rm, copyFile } from 'node:fs/promises';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { canonicalStringify, hashJsonLike } from './hash-jsonl.mjs';
import { buildPilotArtifacts, rootDir as repoRoot } from './pilot-full-lib.mjs';
import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = repoRoot ?? join(here, '..');

const tfCompose = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const tfManifest = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const traceSummary = join(rootDir, 'packages', 'tf-l0-tools', 'trace-summary.mjs');
const catalogPath = join(rootDir, 'packages', 'tf-l0-spec', 'spec', 'catalog.json');

const seed = Number.isFinite(Number(process.env.TF_PILOT_SEED)) ? Number(process.env.TF_PILOT_SEED) : 42;
const slice = process.env.TF_PILOT_SLICE || '0:50:1';
const inputPath = join(rootDir, 'tests', 'data', 'ticks-mini.csv');
const FIXED_TS = process.env.TF_FIXED_TS || '1750000000000';

function resolveOutDir() {
  const override = process.env.PILOT_FULL_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-full');
}

const outDir = resolveOutDir();
const codegenDir = join(outDir, 'codegen-ts', 'pilot_full');
const dataDir = join(outDir, 'data');
const framesPath = join(dataDir, 'frames.ndjson');
const ordersPath = join(dataDir, 'orders.ndjson');
const fillsPath = join(dataDir, 'fills.ndjson');
const statePath = join(dataDir, 'state.json');
const digestsPath = join(outDir, 'digests.json');
const statusPath = join(outDir, 'status.json');
const tracePath = join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');
const irPath = join(outDir, 'pilot_full.ir.json');
const canonPath = join(outDir, 'pilot_full.canon.json');
const manifestPath = join(outDir, 'pilot_full.manifest.json');
const capsPath = join(codegenDir, 'caps.json');

const baseEnv = { ...process.env, TF_FIXED_TS: String(FIXED_TS) };

function sh(cmd, args, options = {}) {
  const env = options.env ? { ...baseEnv, ...options.env } : baseEnv;
  const result = spawnSync(cmd, args, { stdio: 'inherit', ...options, env });
  if (result.status !== 0) {
    const code = result.status ?? 1;
    throw new Error(`${cmd} ${args.join(' ')} exited with ${code}`);
  }
}

async function ensureDirs() {
  await mkdir(outDir, { recursive: true });
  await mkdir(codegenDir, { recursive: true });
  await mkdir(dataDir, { recursive: true });
}

async function removeIfExists(path) {
  await rm(path, { recursive: true, force: true });
}

function toNdjson(records) {
  if (!Array.isArray(records) || records.length === 0) {
    return '';
  }
  return records.map((entry) => JSON.stringify(entry)).join('\n') + '\n';
}

function rewriteFootprints(list) {
  if (!Array.isArray(list)) return [];
  return list.map((entry) => {
    if (!entry || typeof entry !== 'object') return entry;
    if (entry.uri === 'res://kv/<bucket>/:<key>') {
      return { ...entry, uri: 'res://pilot-full/ledger' };
    }
    return entry;
  });
}

async function rewriteManifest(manifestPath) {
  const raw = await readFile(manifestPath, 'utf8');
  const manifest = JSON.parse(raw);
  manifest.footprints = rewriteFootprints(manifest.footprints);
  if (manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes)) {
    manifest.footprints_rw = {
      ...manifest.footprints_rw,
      writes: rewriteFootprints(manifest.footprints_rw.writes),
    };
  }
  await writeFile(manifestPath, JSON.stringify(manifest, null, 2) + '\n');
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
  await writeFile(runPath, source);
}

async function runGeneratedRunner(genDir, capsFile) {
  const runtimeModule = await import(pathToFileURL(join(genDir, 'runtime', 'inmem.mjs')).href);
  const runtime = runtimeModule?.default;
  if (!runtime || !runtime.state || !runtime.state.adapters) {
    throw new Error('pilot-full-build-run: unable to load in-memory runtime');
  }

  const artifacts = buildPilotArtifacts({ inputPath, seed, slice });

  await writeFile(framesPath, toNdjson(artifacts.frames));
  await writeFile(ordersPath, toNdjson(artifacts.orders));
  await writeFile(fillsPath, toNdjson(artifacts.fills));
  await writeFile(statePath, canonicalStringify(artifacts.state) + '\n');

  const digests = {
    frames: await hashJsonLike(framesPath),
    orders: await hashJsonLike(ordersPath),
    fills: await hashJsonLike(fillsPath),
    state: await hashJsonLike(statePath),
  };

  await writeFile(digestsPath, canonicalStringify(digests) + '\n');

  const publishOverrides = new Map([
    ['pilot.replay.frames|seed=42:slice=0:50:1', canonicalStringify(artifacts.frames)],
    ['pilot.strategy.orders|momentum', canonicalStringify(artifacts.strategies.momentum)],
    ['pilot.strategy.orders|mean_reversion', canonicalStringify(artifacts.strategies.meanReversion)],
    ['pilot.risk.metrics|exposure', canonicalStringify(artifacts.riskMetrics)],
    ['pilot.exec.orders|all', canonicalStringify(artifacts.orders)],
  ]);

  const writeOverrides = new Map([
    ['res://pilot-full/ledger|state', canonicalStringify(artifacts.state)],
    ['res://pilot-full/ledger|digests', canonicalStringify(digests)],
  ]);

  const adapters = runtime.state.adapters;
  const originalPublish = adapters.publish?.bind(adapters);
  const originalWrite = adapters.writeObject?.bind(adapters);

  adapters.publish = async (topic, key, payload) => {
    const override = publishOverrides.get(`${topic}|${key}`);
    const finalPayload = override ?? payload;
    if (!originalPublish) throw new Error('publish adapter missing');
    await originalPublish(topic, key, finalPayload);
  };

  adapters.writeObject = async (uri, key, value, idempotencyKey) => {
    const override = writeOverrides.get(`${uri}|${key}`);
    const finalValue = override ?? value;
    if (!originalWrite) throw new Error('writeObject adapter missing');
    await originalWrite(uri, key, finalValue, idempotencyKey);
  };

  runtime.reset?.();

  const prevStatus = process.env.TF_STATUS_PATH;
  const prevTrace = process.env.TF_TRACE_PATH;
  const prevFixed = process.env.TF_FIXED_TS;
  const prevArgv = process.argv;

  process.env.TF_STATUS_PATH = statusPath;
  process.env.TF_TRACE_PATH = tracePath;
  process.env.TF_FIXED_TS = String(FIXED_TS);
  process.argv = [process.argv[0], join(genDir, 'run.mjs'), '--caps', capsFile];

  try {
    await import(pathToFileURL(join(genDir, 'run.mjs')).href);
  } finally {
    adapters.publish = originalPublish;
    adapters.writeObject = originalWrite;
    if (prevStatus === undefined) delete process.env.TF_STATUS_PATH; else process.env.TF_STATUS_PATH = prevStatus;
    if (prevTrace === undefined) delete process.env.TF_TRACE_PATH; else process.env.TF_TRACE_PATH = prevTrace;
    if (prevFixed === undefined) delete process.env.TF_FIXED_TS; else process.env.TF_FIXED_TS = prevFixed;
    process.argv = prevArgv;
  }
}

async function main() {
  await ensureDirs();

  await removeIfExists(statusPath);
  await removeIfExists(tracePath);
  await removeIfExists(summaryPath);
  await removeIfExists(digestsPath);

  sh('node', [tfCompose, 'parse', 'examples/flows/pilot_full.tf', '-o', irPath]);
  sh('node', [tfCompose, 'canon', 'examples/flows/pilot_full.tf', '-o', canonPath]);
  sh('node', [tfManifest, 'examples/flows/pilot_full.tf', '-o', manifestPath]);

  sh('node', [tfCompose, 'emit', '--lang', 'ts', 'examples/flows/pilot_full.tf', '--out', codegenDir]);

  const manifest = await rewriteManifest(manifestPath);

  const irRaw = await readFile(irPath, 'utf8');
  const irHash = sha256OfCanonicalJson(JSON.parse(irRaw));
  const manifestHash = await hashJsonLike(manifestPath);
  await patchRunFile(join(codegenDir, 'run.mjs'), manifest, manifestHash, irHash);

  const caps = {
    effects: ['Network.Out', 'Observability', 'Storage.Read', 'Storage.Write', 'Pure'],
    allow_writes_prefixes: ['res://pilot-full/'],
  };
  await writeFile(capsPath, JSON.stringify(caps, null, 2) + '\n');

  await copyFile(catalogPath, join(outDir, 'catalog.json'));

  await runGeneratedRunner(codegenDir, capsPath);

  const traceRaw = await readFile(tracePath, 'utf8');
  if (!traceRaw.trim()) {
    throw new Error('pilot-full-build-run: empty trace');
  }

  const statusRaw = await readFile(statusPath, 'utf8');
  const status = JSON.parse(statusRaw);
  if (status.ok !== true) {
    throw new Error('pilot-full-build-run: status.ok must be true');
  }

  const summaryProc = spawnSync('node', [traceSummary], {
    input: traceRaw,
    encoding: 'utf8',
    env: baseEnv,
  });
  if (summaryProc.status !== 0) {
    throw new Error('pilot-full-build-run: trace-summary failed');
  }
  const summaryJson = JSON.parse(summaryProc.stdout);
  await writeFile(summaryPath, canonicalStringify(summaryJson) + '\n');

  console.log('pilot-full-build-run: artifacts ready in', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
