#!/usr/bin/env node
import { mkdirSync, writeFileSync, readFileSync, rmSync, existsSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { hashFile } from './hash-jsonl.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const pilotOutRel = process.env.TF_PILOT_OUT_DIR ?? 'out/0.4/pilot-l0';
const pilotOut = join(repoRoot, pilotOutRel);
const outRoot = dirname(pilotOut);
const goldenDir = join(pilotOut, 'golden');
const codegenDir = join(pilotOut, 'codegen-ts', 'pilot_min');

mkdirSync(pilotOut, { recursive: true });

const irPath = join(pilotOut, 'pilot_min.ir.json');
const canonPath = join(pilotOut, 'pilot_min.canon.json');
const manifestPath = join(pilotOut, 'pilot_min.manifest.json');
const statusPath = join(pilotOut, 'status.json');
const tracePath = join(pilotOut, 'trace.jsonl');
const summaryPath = join(pilotOut, 'summary.json');
const digestsPath = join(pilotOut, 'digests.json');

const tfBinary = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const manifestBinary = join(repoRoot, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const traceSummaryBinary = join(repoRoot, 'packages', 'tf-l0-tools', 'trace-summary.mjs');

function sh(cmd, args, opts = {}) {
  const result = spawnSync(cmd, args, { stdio: 'inherit', ...opts });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

function rewriteFootprints(list) {
  if (!Array.isArray(list)) return [];
  return list.map((entry) => {
    if (!entry || typeof entry !== 'object') return entry;
    if (typeof entry.uri === 'string' && entry.uri.startsWith('res://kv/')) {
      const updated = { ...entry, uri: 'res://ledger/pilot' };
      if (updated.notes === 'seed') updated.notes = 'pilot ledger write';
      return updated;
    }
    return entry;
  });
}

function rewriteManifest(path) {
  const raw = readFileSync(path, 'utf8');
  const manifest = JSON.parse(raw);
  manifest.footprints = rewriteFootprints(manifest.footprints);
  if (manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes)) {
    manifest.footprints_rw = {
      ...manifest.footprints_rw,
      writes: rewriteFootprints(manifest.footprints_rw.writes),
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
  const next = `${prefix}${JSON.stringify(manifest)};\n${suffix}`;
  writeFileSync(runPath, next);
}

function patchRunClock(runPath) {
  const source = readFileSync(runPath, 'utf8');
  const needle = "import { parseArgs } from 'node:util';\n";
  const inject = `${needle}\nconst __tfDeterministicClock = (() => {\n  let counter = 0n;\n  const base = 1690000000000n * 1_000_000n;\n  return {\n    nowNs() {\n      const value = base + counter * 1_000_000n;\n      counter += 1n;\n      return value;\n    }\n  };\n})();\nif (!globalThis.__tf_clock) {\n  globalThis.__tf_clock = __tfDeterministicClock;\n}\n`;
  if (source.includes('__tfDeterministicClock')) {
    return;
  }
  if (!source.includes(needle)) {
    throw new Error('unable to patch run.mjs for deterministic clock');
  }
  const updated = source.replace(needle, inject);
  writeFileSync(runPath, updated);
}

function cleanOutput(paths) {
  for (const path of paths) {
    try {
      rmSync(path, { recursive: true, force: true });
    } catch {}
  }
}

cleanOutput([codegenDir, statusPath, tracePath, summaryPath, digestsPath, goldenDir]);
mkdirSync(codegenDir, { recursive: true });
mkdirSync(goldenDir, { recursive: true });

sh('node', [tfBinary, 'parse', 'examples/flows/pilot_min.tf', '-o', irPath]);
sh('node', [tfBinary, 'canon', 'examples/flows/pilot_min.tf', '-o', canonPath]);
sh('node', [manifestBinary, 'examples/flows/pilot_min.tf', '-o', manifestPath]);
const manifest = rewriteManifest(manifestPath);

sh('node', [tfBinary, 'emit', '--lang', 'ts', 'examples/flows/pilot_min.tf', '--out', codegenDir]);
const runPath = join(codegenDir, 'run.mjs');
patchRunManifest(runPath, manifest);
patchRunClock(runPath);

const caps = {
  effects: ['Network.Out', 'Storage.Write', 'Observability', 'Pure'],
  allow_writes_prefixes: ['res://ledger/'],
};
writeFileSync(join(codegenDir, 'caps.json'), `${JSON.stringify(caps, null, 2)}\n`);

const env = { ...process.env, TF_STATUS_PATH: statusPath, TF_TRACE_PATH: tracePath };
sh('node', [runPath, '--caps', join(codegenDir, 'caps.json')], { env });

const traceRaw = readFileSync(tracePath, 'utf8');
if (!traceRaw.trim()) {
  console.error('empty trace emitted by generated runner');
  process.exit(1);
}

const statusRaw = readFileSync(statusPath, 'utf8');
const status = JSON.parse(statusRaw);
status.ok = status.ok !== false;
status.ops = Number.isFinite(status.ops) ? Number(status.ops) : 0;
if (Array.isArray(status.effects)) {
  const filtered = status.effects.filter((entry) => typeof entry === 'string');
  status.effects = Array.from(new Set(filtered)).sort();
} else {
  status.effects = [];
}
status.manifest_path = manifestPath;
writeFileSync(statusPath, `${JSON.stringify(status, null, 2)}\n`);

const summaryProc = spawnSync('node', [traceSummaryBinary], { input: traceRaw, encoding: 'utf8' });
if (summaryProc.status !== 0) {
  process.exit(summaryProc.status ?? 1);
}
const summaryJson = JSON.parse(summaryProc.stdout);
writeFileSync(summaryPath, `${JSON.stringify(summaryJson)}\n`);

const digests = {
  status: hashFile(statusPath),
  trace: hashFile(tracePath),
  summary: hashFile(summaryPath),
  ir: hashFile(irPath),
  canon: hashFile(canonPath),
  manifest: hashFile(manifestPath),
};
writeFileSync(digestsPath, `${JSON.stringify(digests, null, 2)}\n`);

const signingIrPath = join(repoRoot, 'out', '0.4', 'ir', 'signing.ir.json');
if (!existsSync(signingIrPath)) {
  mkdirSync(dirname(signingIrPath), { recursive: true });
  sh('node', [tfBinary, 'parse', 'examples/flows/signing.tf', '-o', signingIrPath]);
}

writeFileSync(join(goldenDir, 'digests.json'), readFileSync(digestsPath));
writeFileSync(join(goldenDir, 'status.json'), readFileSync(statusPath));
writeFileSync(join(goldenDir, 'summary.json'), readFileSync(summaryPath));
writeFileSync(join(goldenDir, 'trace.jsonl'), readFileSync(tracePath));

console.log('pilot build complete');
