#!/usr/bin/env node
import { mkdirSync, writeFileSync, readFileSync, rmSync, cpSync } from 'node:fs';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { spawnSync } from 'node:child_process';
import { canonicalize, canonicalStringify, hashJsonFile } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const workdir = process.env.TF_PILOT_WORKDIR;
const outRoot = workdir
  ? (isAbsolute(workdir) ? workdir : join(root, workdir))
  : join(root, 'out', '0.4');
const pilotDir = join(outRoot, 'pilot-l0');
const codegenDir = join(pilotDir, 'codegen-ts', 'pilot_min');
const goldenDir = join(pilotDir, 'golden');

rmSync(pilotDir, { recursive: true, force: true });
mkdirSync(codegenDir, { recursive: true });
mkdirSync(goldenDir, { recursive: true });

const tfCli = join(root, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const tfManifestCli = join(root, 'packages', 'tf-compose', 'bin', 'tf-manifest.mjs');
const traceSummaryCli = join(root, 'packages', 'tf-l0-tools', 'trace-summary.mjs');
const flowPath = join(root, 'examples', 'flows', 'pilot_min.tf');

const irPath = join(pilotDir, 'pilot_min.ir.json');
const canonPath = join(pilotDir, 'pilot_min.canon.json');
const manifestPath = join(pilotDir, 'pilot_min.manifest.json');
const statusPath = join(pilotDir, 'status.json');
const tracePath = join(pilotDir, 'trace.jsonl');
const summaryPath = join(pilotDir, 'summary.json');
const digestsPath = join(pilotDir, 'digests.json');

function sh(command, args, opts = {}) {
  const result = spawnSync(command, args, { stdio: 'inherit', ...opts });
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
  writeFileSync(path, JSON.stringify(manifest, null, 2) + '\n', 'utf8');
  return manifest;
}

function normalizeStatus(raw) {
  const effects = Array.isArray(raw.effects) ? Array.from(new Set(raw.effects.filter((e) => typeof e === 'string'))).sort() : [];
  const ops = Number.isFinite(raw.ops) ? raw.ops : 0;
  const ok = raw.ok === true;
  return { ok, ops, effects };
}

function normalizeTraceLine(record) {
  const ordered = {
    ts: Number(record.ts ?? 0),
    prim_id: record.prim_id ?? '',
    args: canonicalize(record.args ?? {}),
    region: typeof record.region === 'string' ? record.region : '',
    effect: typeof record.effect === 'string' ? record.effect : '',
  };
  return JSON.stringify(ordered);
}

function appendNodeOptions(env, modulePath) {
  const existing = env.NODE_OPTIONS ? `${env.NODE_OPTIONS} ` : '';
  const next = `${existing}--import=${pathToFileURL(modulePath).href}`.trim();
  return { ...env, NODE_OPTIONS: next };
}

sh('node', [tfCli, 'parse', flowPath, '-o', irPath]);
sh('node', [tfCli, 'canon', flowPath, '-o', canonPath]);
sh('node', [tfManifestCli, flowPath, '-o', manifestPath]);
const manifest = rewriteManifest(manifestPath);

sh('node', [tfCli, 'emit', '--lang', 'ts', flowPath, '--out', codegenDir]);

const runPath = join(codegenDir, 'run.mjs');
const runSource = readFileSync(runPath, 'utf8');
const marker = 'const MANIFEST = ';
const idx = runSource.indexOf(marker);
if (idx !== -1) {
  const start = idx + marker.length;
  const suffixIdx = runSource.indexOf(';\n', start);
  if (suffixIdx !== -1) {
    const prefix = runSource.slice(0, start);
    const suffix = runSource.slice(suffixIdx);
    const updated = `${prefix}${JSON.stringify(manifest)}${suffix}`;
    writeFileSync(runPath, updated, 'utf8');
  }
}

const caps = {
  effects: ['Network.Out', 'Storage.Write', 'Observability', 'Pure'],
  allow_writes_prefixes: ['res://ledger/'],
};
writeFileSync(join(codegenDir, 'caps.json'), JSON.stringify(caps, null, 2) + '\n', 'utf8');

for (const target of [statusPath, tracePath, summaryPath]) {
  rmSync(target, { force: true });
}

const env = appendNodeOptions(
  {
    ...process.env,
    TF_STATUS_PATH: statusPath,
    TF_TRACE_PATH: tracePath,
  },
  join(here, 'pilot-clock.mjs'),
);

sh('node', [runPath, '--caps', join(codegenDir, 'caps.json')], { env });

const traceRaw = readFileSync(tracePath, 'utf8').trim();
if (!traceRaw) {
  console.error('pilot-build-run: empty trace output');
  process.exit(1);
}
const traceLines = traceRaw.split(/\r?\n/).filter((line) => line.length > 0);
const normalizedTrace = traceLines.map((line) => {
  const parsed = JSON.parse(line);
  return normalizeTraceLine(parsed);
});
writeFileSync(tracePath, normalizedTrace.join('\n') + '\n', 'utf8');

const statusRaw = JSON.parse(readFileSync(statusPath, 'utf8'));
const statusNorm = normalizeStatus(statusRaw);
writeFileSync(statusPath, JSON.stringify(statusNorm, null, 2) + '\n', 'utf8');

const summaryProc = spawnSync('node', [traceSummaryCli], {
  input: normalizedTrace.join('\n') + '\n',
  encoding: 'utf8',
});
if (summaryProc.status !== 0) {
  process.exit(summaryProc.status ?? 1);
}
const summaryJson = JSON.parse(summaryProc.stdout);
writeFileSync(summaryPath, canonicalStringify(summaryJson) + '\n', 'utf8');

const digests = {
  status: hashJsonFile(statusPath),
  trace: hashJsonFile(tracePath, { jsonl: true }),
  summary: hashJsonFile(summaryPath),
  ir: hashJsonFile(irPath),
  canon: hashJsonFile(canonPath),
  manifest: hashJsonFile(manifestPath),
};
writeFileSync(digestsPath, canonicalStringify(digests) + '\n', 'utf8');

cpSync(digestsPath, join(goldenDir, 'digests.json'));
cpSync(statusPath, join(goldenDir, 'status.json'));
cpSync(summaryPath, join(goldenDir, 'summary.json'));
cpSync(tracePath, join(goldenDir, 'trace.jsonl'));

console.log('pilot-build-run complete');
