#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile, rm } from 'node:fs/promises';
import { copyFileSync } from 'node:fs';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { canonicalStringify, hashJsonLike } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');

function resolveOutDir() {
  const override = process.env.PILOT_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-l0');
}

const outDir = resolveOutDir();
const goldenDir = join(outDir, 'golden');
const tfCompose = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const tfManifest = join(rootDir, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const traceSummary = join(rootDir, 'packages', 'tf-l0-tools', 'trace-summary.mjs');
const flowPath = join(rootDir, 'examples', 'flows', 'pilot_min.tf');
const ledgerUri = 'res://ledger/pilot';

function sh(cmd, args, options = {}) {
  const result = spawnSync(cmd, args, { stdio: 'inherit', ...options });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

function rewriteFootprints(list) {
  if (!Array.isArray(list)) return [];
  return list.map((entry) => {
    if (!entry || typeof entry !== 'object') return entry;
    if (typeof entry.uri === 'string' && entry.uri.startsWith('res://kv/')) {
      const updated = { ...entry, uri: ledgerUri };
      if (updated.notes === 'seed') updated.notes = 'pilot ledger write';
      return updated;
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

async function patchRunManifest(runPath, manifest) {
  const source = await readFile(runPath, 'utf8');
  const marker = 'const MANIFEST = ';
  const idx = source.indexOf(marker);
  if (idx === -1) return;
  const start = idx + marker.length;
  const remainder = source.slice(start);
  const end = remainder.indexOf(';\n');
  if (end === -1) return;
  const prefix = source.slice(0, start);
  const suffix = remainder.slice(end + 2);
  const next = `${prefix}${JSON.stringify(manifest)};\n${suffix}`;
  await writeFile(runPath, next);
}

function createDeterministicClock(startMs = 1_690_000_000_000, stepMs = 1) {
  let current = BigInt(startMs) * 1_000_000n;
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
  const prevArgv = process.argv;
  const prevClock = globalThis.__tf_clock;

  process.env.TF_STATUS_PATH = statusPath;
  process.env.TF_TRACE_PATH = tracePath;
  globalThis.__tf_clock = createDeterministicClock();
  process.argv = [process.argv[0], join(genDir, 'run.mjs'), '--caps', capsPath];

  try {
    await import(pathToFileURL(join(genDir, 'run.mjs')).href);
  } finally {
    if (prevStatus === undefined) delete process.env.TF_STATUS_PATH;
    else process.env.TF_STATUS_PATH = prevStatus;
    if (prevTrace === undefined) delete process.env.TF_TRACE_PATH;
    else process.env.TF_TRACE_PATH = prevTrace;
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

async function ensureDirs() {
  await mkdir(outDir, { recursive: true });
  await mkdir(goldenDir, { recursive: true });
}

async function removeIfExists(path) {
  await rm(path, { recursive: true, force: true });
}

async function main() {
  await ensureDirs();

  const irPath = join(outDir, 'pilot_min.ir.json');
  const canonPath = join(outDir, 'pilot_min.canon.json');
  const manifestPath = join(outDir, 'pilot_min.manifest.json');

  sh('node', [tfCompose, 'parse', flowPath, '-o', irPath]);
  sh('node', [tfCompose, 'canon', flowPath, '-o', canonPath]);
  sh('node', [tfManifest, flowPath, '-o', manifestPath]);
  const manifest = await rewriteManifest(manifestPath);

  const genDir = join(outDir, 'codegen-ts', 'pilot_min');
  await mkdir(genDir, { recursive: true });
  sh('node', [tfCompose, 'emit', '--lang', 'ts', flowPath, '--out', genDir]);
  await patchRunManifest(join(genDir, 'run.mjs'), manifest);

  const caps = {
    effects: ['Network.Out', 'Storage.Write', 'Observability', 'Pure'],
    allow_writes_prefixes: ['res://ledger/'],
  };
  await writeFile(join(genDir, 'caps.json'), JSON.stringify(caps, null, 2) + '\n');

  const statusPath = join(outDir, 'status.json');
  const tracePath = join(outDir, 'trace.jsonl');
  const summaryPath = join(outDir, 'summary.json');

  await removeIfExists(statusPath);
  await removeIfExists(tracePath);
  await removeIfExists(summaryPath);

  await runGeneratedRunner(genDir, join(genDir, 'caps.json'), statusPath, tracePath);

  const traceRaw = await readFile(tracePath, 'utf8');
  if (!traceRaw.trim()) {
    throw new Error('pilot-build-run: empty trace output');
  }
  const status = JSON.parse(await readFile(statusPath, 'utf8'));
  if (status.ok !== true) throw new Error('pilot-build-run: status.ok must be true');
  if (!Number.isFinite(status.ops) || status.ops < 2) throw new Error('pilot-build-run: status.ops too low');
  if (!Array.isArray(status.effects) || !status.effects.includes('Network.Out') || !status.effects.includes('Storage.Write')) {
    throw new Error('pilot-build-run: status missing required effects');
  }
  status.manifest_path = manifestPath;
  await writeFile(statusPath, JSON.stringify(status, null, 2) + '\n');

  const summaryProc = spawnSync('node', [traceSummary], {
    input: traceRaw,
    encoding: 'utf8',
  });
  if (summaryProc.status !== 0) {
    throw new Error('pilot-build-run: trace-summary failed');
  }
  const summaryJson = JSON.parse(summaryProc.stdout);
  const canonicalSummary = canonicalStringify(summaryJson);
  await writeFile(summaryPath, canonicalSummary + '\n');

  const digests = {
    status: await hashJsonLike(statusPath),
    trace: await hashJsonLike(tracePath),
    summary: await hashJsonLike(summaryPath),
    ir: await hashJsonLike(irPath),
    canon: await hashJsonLike(canonPath),
    manifest: await hashJsonLike(manifestPath),
  };

  const digestsJson = JSON.stringify(digests, null, 2) + '\n';
  await writeFile(join(outDir, 'digests.json'), digestsJson);

  copyFileSync(statusPath, join(goldenDir, 'status.json'));
  copyFileSync(tracePath, join(goldenDir, 'trace.jsonl'));
  copyFileSync(summaryPath, join(goldenDir, 'summary.json'));
  await writeFile(join(goldenDir, 'digests.json'), digestsJson);

  console.log('pilot-build-run: completed artifacts in', outDir);
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
