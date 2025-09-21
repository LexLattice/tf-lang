#!/usr/bin/env node
import { mkdirSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const __dir = dirname(fileURLToPath(import.meta.url));
const outDir = join(__dir, '..', 'out', '0.4', 'pilot-l0');
mkdirSync(outDir, { recursive: true });

// 1) Parse, check, canon, manifest
const irPath = join(outDir, 'pilot_min.ir.json');
const canonPath = join(outDir, 'pilot_min.canon.json');
const manPath = join(outDir, 'pilot_min.manifest.json');
const ledgerUri = 'res://ledger/pilot';

function sh(cmd, args, opts = {}) {
  const r = spawnSync(cmd, args, { stdio: 'inherit', ...opts });
  if (r.status !== 0) process.exit(r.status ?? 1);
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
  const next = `${prefix}${JSON.stringify(manifest)};\n${suffix}`;
  writeFileSync(runPath, next);
}

sh('node', ['packages/tf-compose/bin/tf.mjs', 'parse', 'examples/flows/pilot_min.tf', '-o', irPath]);
sh('node', ['packages/tf-compose/bin/tf.mjs', 'canon', 'examples/flows/pilot_min.tf', '-o', canonPath]);
sh('node', ['packages/tf-compose/bin/tf-manifest.mjs', 'examples/flows/pilot_min.tf', '-o', manPath]);
const manifest = rewriteManifest(manPath);

// 2) Generate TS + caps
const genDir = join(outDir, 'codegen-ts', 'pilot_min');
mkdirSync(genDir, { recursive: true });
sh('node', ['packages/tf-compose/bin/tf.mjs', 'emit', '--lang', 'ts', 'examples/flows/pilot_min.tf', '--out', genDir]);
patchRunManifest(join(genDir, 'run.mjs'), manifest);

const caps = {
  effects: ['Network.Out', 'Storage.Write', 'Observability', 'Pure'],
  allow_writes_prefixes: ['res://ledger/']
};
writeFileSync(join(genDir, 'caps.json'), JSON.stringify(caps) + '\n');

// 3) Run with status + trace + summarize
const statusPath = join(outDir, 'status.json');
const tracePath = join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');

for (const path of [statusPath, tracePath, summaryPath]) {
  try {
    rmSync(path);
  } catch (err) {
    if (err?.code !== 'ENOENT') throw err;
  }
}

const env = { ...process.env, TF_STATUS_PATH: statusPath, TF_TRACE_PATH: tracePath };
sh('node', [join(genDir, 'run.mjs'), '--caps', join(genDir, 'caps.json')], { env });

const trace = readFileSync(tracePath, 'utf8');
if (!trace.trim()) {
  console.error('empty trace?');
  process.exit(1);
}
const statusRaw = readFileSync(statusPath, 'utf8');
const statusJson = JSON.parse(statusRaw);

if (statusJson.ok !== true) {
  console.error('pilot status missing ok=true');
  process.exit(1);
}
if (typeof statusJson.ops !== 'number' || statusJson.ops < 2) {
  console.error('pilot status ops too low');
  process.exit(1);
}
if (!Array.isArray(statusJson.effects) ||
    !statusJson.effects.includes('Network.Out') ||
    !statusJson.effects.includes('Storage.Write')) {
  console.error('pilot status missing required effects');
  process.exit(1);
}

statusJson.manifest_path = manPath;
writeFileSync(statusPath, `${JSON.stringify(statusJson, null, 2)}\n`);

const summary = spawnSync('node', ['packages/tf-l0-tools/trace-summary.mjs'], {
  input: trace,
  encoding: 'utf8'
});
if (summary.status !== 0) process.exit(summary.status ?? 1);

const summaryJson = JSON.parse(summary.stdout);
writeFileSync(summaryPath, `${JSON.stringify(summaryJson)}\n`);

console.log(`wrote status=${statusPath} trace=${tracePath} summary=${summaryPath} manifest=${manPath}`);
