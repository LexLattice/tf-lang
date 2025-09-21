#!/usr/bin/env node
import { mkdirSync, writeFileSync, readFileSync, rmSync, copyFileSync } from 'node:fs';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { hashJsonFile } from './hash-jsonl.mjs';

const __dir = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dir, '..');
const baseOutDir = process.env.TF_PILOT_OUT_DIR
  ? resolve(repoRoot, process.env.TF_PILOT_OUT_DIR)
  : join(repoRoot, 'out', '0.4', 'pilot-l0');
const outDir = baseOutDir;
const parityDir = join(baseOutDir, '..', '..', 'parity');
const flowPath = join(repoRoot, 'examples', 'flows', 'pilot_min.tf');
const irPath = join(outDir, 'pilot_min.ir.json');
const canonPath = join(outDir, 'pilot_min.canon.json');
const manifestPath = join(outDir, 'pilot_min.manifest.json');
const genDir = join(outDir, 'codegen-ts', 'pilot_min');
const capsPath = join(genDir, 'caps.json');
const statusPath = join(outDir, 'status.json');
const tracePath = join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');
const digestsPath = join(outDir, 'digests.json');
const goldenDir = join(outDir, 'golden');

const deterministicClockEpochMs = 1700000000000n;

mkdirSync(outDir, { recursive: true });
mkdirSync(parityDir, { recursive: true });

function sh(cmd, args, opts = {}) {
  const res = spawnSync(cmd, args, { stdio: 'inherit', ...opts });
  if (res.status !== 0) {
    process.exit(res.status ?? 1);
  }
}

function safeRm(path, options = {}) {
  try {
    rmSync(path, { force: true, recursive: true, ...options });
  } catch (err) {
    if (err?.code !== 'ENOENT') throw err;
  }
}

function rewriteFootprints(list) {
  if (!Array.isArray(list)) return [];
  return list.map((entry) => {
    if (!entry || typeof entry !== 'object') return entry;
    if (typeof entry.uri === 'string' && entry.uri.startsWith('res://kv/')) {
      const updated = { ...entry, uri: 'res://ledger/pilot' };
      if (updated.notes === 'seed') {
        updated.notes = 'pilot ledger write';
      }
      return updated;
    }
    return entry;
  });
}

function rewriteManifest(path) {
  const manifestRaw = readFileSync(path, 'utf8');
  const manifest = JSON.parse(manifestRaw);
  manifest.footprints = rewriteFootprints(manifest.footprints);
  if (manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes)) {
    manifest.footprints_rw = {
      ...manifest.footprints_rw,
      writes: rewriteFootprints(manifest.footprints_rw.writes)
    };
  }
  writeFileSync(path, `${JSON.stringify(manifest, null, 2)}\n`);
  return manifest;
}

function patchRunManifest(runPath, manifest) {
  const source = readFileSync(runPath, 'utf8');
  const marker = 'const MANIFEST = ';
  const idx = source.indexOf(marker);
  if (idx === -1) return;
  const start = idx + marker.length;
  const remainder = source.slice(start);
  const end = remainder.indexOf(';\n');
  if (end === -1) return;
  const prefix = source.slice(0, start);
  const suffix = remainder.slice(end + 2);
  let next = `${prefix}${JSON.stringify(manifest)};\n${suffix}`;
  if (!next.includes('__pilot_clock_marker__')) {
    const inject = `\n// __pilot_clock_marker__\nif (!globalThis.__tf_clock || globalThis.__tf_clock.__pilot_clock !== true) {\n  const epochMs = ${deterministicClockEpochMs}n;\n  let tick = 0n;\n  globalThis.__tf_clock = {\n    __pilot_clock: true,\n    nowNs() {\n      const currentMs = epochMs + tick;\n      tick += 1n;\n      return currentMs * 1_000_000n;\n    }\n  };\n}\n`;
    const irMarker = '\nconst ir = ';
    const irIdx = next.indexOf(irMarker);
    if (irIdx !== -1) {
      next = `${next.slice(0, irIdx)}${inject}${next.slice(irIdx)}`;
    } else {
      next = `${next}${inject}`;
    }
  }
  writeFileSync(runPath, next);
}

function prepareDeterministicClockEnv(env) {
  return {
    ...env,
    TF_CLOCK_EPOCH_MS: String(deterministicClockEpochMs),
  };
}

function ensureCleanOutputs() {
  for (const path of [statusPath, tracePath, summaryPath, digestsPath]) {
    safeRm(path);
  }
  safeRm(genDir);
  safeRm(join(outDir, 'codegen-ts'));
  mkdirSync(genDir, { recursive: true });
  safeRm(goldenDir);
  mkdirSync(goldenDir, { recursive: true });
}

async function main() {
  ensureCleanOutputs();

  sh('node', ['packages/tf-compose/bin/tf.mjs', 'parse', flowPath, '-o', irPath]);
  sh('node', ['packages/tf-compose/bin/tf.mjs', 'canon', flowPath, '-o', canonPath]);
  sh('node', ['packages/tf-compose/bin/tf-manifest.mjs', flowPath, '-o', manifestPath]);
  const manifest = rewriteManifest(manifestPath);

  sh('node', ['packages/tf-compose/bin/tf.mjs', 'emit', '--lang', 'ts', flowPath, '--out', genDir]);
  patchRunManifest(join(genDir, 'run.mjs'), manifest);

  const caps = {
    effects: ['Network.Out', 'Storage.Write', 'Observability', 'Pure'],
    allow_writes_prefixes: ['res://ledger/'],
  };
  writeFileSync(capsPath, `${JSON.stringify(caps, null, 2)}\n`);

  const env = prepareDeterministicClockEnv({ ...process.env, TF_STATUS_PATH: statusPath, TF_TRACE_PATH: tracePath });
  sh('node', [join(genDir, 'run.mjs'), '--caps', capsPath], { env });

  const trace = readFileSync(tracePath, 'utf8');
  if (!trace.trim()) {
    throw new Error('pilot-build-run: empty trace output');
  }
  const status = JSON.parse(readFileSync(statusPath, 'utf8'));
  if (status.ok !== true) {
    throw new Error('pilot-build-run: status missing ok=true');
  }
  if (!Number.isFinite(status.ops) || status.ops < 5) {
    throw new Error('pilot-build-run: status.ops unexpected');
  }
  if (!Array.isArray(status.effects) || status.effects.length === 0) {
    throw new Error('pilot-build-run: status.effects missing');
  }
  if (Object.prototype.hasOwnProperty.call(status, 'manifest_path')) {
    delete status.manifest_path;
  }
  writeFileSync(statusPath, `${JSON.stringify(status, null, 2)}\n`);

  const summary = spawnSync('node', ['packages/tf-l0-tools/trace-summary.mjs'], { input: trace, encoding: 'utf8' });
  if (summary.status !== 0) {
    throw new Error('pilot-build-run: trace-summary failed');
  }
  const summaryJson = JSON.parse(summary.stdout);
  writeFileSync(summaryPath, `${JSON.stringify(summaryJson)}\n`);

  const digests = {
    status: (await hashJsonFile(statusPath)).digest,
    trace: (await hashJsonFile(tracePath)).digest,
    summary: (await hashJsonFile(summaryPath)).digest,
    ir: (await hashJsonFile(irPath)).digest,
    canon: (await hashJsonFile(canonPath)).digest,
    manifest: (await hashJsonFile(manifestPath)).digest,
  };
  writeFileSync(digestsPath, `${JSON.stringify(digests, null, 2)}\n`);

  copyFileSync(digestsPath, join(goldenDir, 'digests.json'));
  copyFileSync(statusPath, join(goldenDir, 'status.json'));
  copyFileSync(summaryPath, join(goldenDir, 'summary.json'));
  copyFileSync(tracePath, join(goldenDir, 'trace.jsonl'));

  console.log('pilot-build-run complete');
}

await main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
