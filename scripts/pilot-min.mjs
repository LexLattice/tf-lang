#!/usr/bin/env node
import { mkdirSync, writeFileSync, readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const __dir = dirname(fileURLToPath(import.meta.url));
const outDir = join(__dir, '..', 'out', '0.4', 'pilot-l0');
mkdirSync(outDir, { recursive: true });

// 1) Parse, check, canon, manifest
const irPath    = join(outDir, 'pilot_min.ir.json');
const canonPath = join(outDir, 'pilot_min.canon.json');
const manPath   = join(outDir, 'pilot_min.manifest.json');

function sh(cmd, args, opts = {}) {
  const r = spawnSync(cmd, args, { stdio: 'inherit', ...opts });
  if (r.status !== 0) process.exit(r.status ?? 1);
}

sh('node', ['packages/tf-compose/bin/tf.mjs', 'parse', 'examples/flows/pilot_min.tf', '-o', irPath]);
sh('node', ['packages/tf-compose/bin/tf.mjs', 'canon', 'examples/flows/pilot_min.tf', '-o', canonPath]);
sh('node', ['packages/tf-compose/bin/tf-manifest.mjs', 'examples/flows/pilot_min.tf', '-o', manPath]);

const manifest = JSON.parse(readFileSync(manPath, 'utf8'));
const fixUri = (entry) => {
  if (!entry || typeof entry !== 'object') return entry;
  if (typeof entry.uri === 'string' && entry.uri.startsWith('res://ledger/')) return entry;
  return { ...entry, uri: 'res://ledger/pilot/:<key>' };
};
if (Array.isArray(manifest.footprints)) {
  manifest.footprints = manifest.footprints.map(fixUri);
}
if (manifest.footprints_rw && Array.isArray(manifest.footprints_rw.writes)) {
  manifest.footprints_rw = {
    ...manifest.footprints_rw,
    writes: manifest.footprints_rw.writes.map(fixUri),
  };
}
writeFileSync(manPath, JSON.stringify(manifest, null, 2) + '\n');

// 2) Generate TS + caps
const genDir = join(outDir, 'codegen-ts', 'pilot_min');
mkdirSync(genDir, { recursive: true });
sh('node', ['packages/tf-compose/bin/tf.mjs', 'emit', '--lang', 'ts', 'examples/flows/pilot_min.tf', '--out', genDir]);

const runPath = join(genDir, 'run.mjs');
const runSrc = readFileSync(runPath, 'utf8');
const manifestLiteral = `const MANIFEST = ${JSON.stringify(manifest)};`;
const updatedRun = runSrc.replace(/const MANIFEST = .*?;\n/s, `${manifestLiteral}\n`);
if (updatedRun === runSrc) {
  console.warn('pilot-min: unable to update manifest literal in run.mjs');
} else {
  writeFileSync(runPath, updatedRun);
}

const caps = {
  effects: ['Network.Out', 'Storage.Write', 'Observability', 'Pure'],
  allow_writes_prefixes: ['res://ledger/']
};
writeFileSync(join(genDir, 'caps.json'), JSON.stringify(caps) + '\n');

// 3) Run with status + trace + summarize
const statusPath = join(outDir, 'status.json');
const tracePath = join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');

const env = { ...process.env, TF_STATUS_PATH: statusPath, TF_TRACE_PATH: tracePath };
sh('node', [join(genDir, 'run.mjs'), '--caps', join(genDir, 'caps.json')], { env });

const trace = readFileSync(tracePath, 'utf8');
if (!trace.trim()) {
  console.error('empty trace?');
  process.exit(1);
}
const summary = spawnSync('node', ['packages/tf-l0-tools/trace-summary.mjs'], {
  input: trace,
  encoding: 'utf8'
});
if (summary.status !== 0) process.exit(summary.status ?? 1);
writeFileSync(summaryPath, summary.stdout.endsWith('\n') ? summary.stdout : summary.stdout + '\n');

console.log(`wrote status=${statusPath} trace=${tracePath} summary=${summaryPath}`);
