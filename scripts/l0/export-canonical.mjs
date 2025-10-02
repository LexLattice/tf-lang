#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

const STRIP_KEYS = new Set([
  'runtime',
  'arrayBindings',
  'debug',
  'trace',
  'instrumentation',
  'x-runtime',
  'x-debug',
  'x-trace',
  'meta',
]);

const args = process.argv.slice(2);
const check = args.includes('--check');
const outIdx = args.indexOf('--out');
if (outIdx === -1 || outIdx === args.length - 1) {
  console.error('Usage: export-canonical.mjs [--check] --out <outDir> <files...>');
  process.exit(2);
}
const outDir = path.resolve(args[outIdx + 1]);
const files = args.filter((arg, idx) => idx > outIdx + 1 && arg !== '--check');

const manifests = new Map(); // manifestPath -> { file: hash }
const errors = [];

function sortKeysDeep(value) {
  if (Array.isArray(value)) {
    return value.map(sortKeysDeep);
  }
  if (value && typeof value === 'object') {
    const out = {};
    for (const key of Object.keys(value).sort()) {
      out[key] = sortKeysDeep(value[key]);
    }
    return out;
  }
  return value;
}

function stripExtras(value, parentKey = null) {
  if (Array.isArray(value)) {
    if (parentKey === 'in' || parentKey === 'out') {
      const out = {};
      value.forEach((entry, idx) => {
        out[String(idx)] = stripExtras(entry);
      });
      return out;
    }
    return value.map((entry) => stripExtras(entry));
  }
  if (value && typeof value === 'object') {
    const out = {};
    for (const [key, child] of Object.entries(value)) {
      if (STRIP_KEYS.has(key)) continue;
      out[key] = stripExtras(child, key);
    }
    if ((parentKey === 'in' || parentKey === 'out') && Object.keys(out).length === 0) {
      return null;
    }
    return out;
  }
  return value;
}

function stableStringify(obj) {
  return `${JSON.stringify(sortKeysDeep(obj), null, 2)}\n`;
}

function sha256(buf) {
  return crypto.createHash('sha256').update(buf).digest('hex');
}

function registerManifest(outPath, hash) {
  const manifestPath = path.join(path.dirname(outPath), 'manifest.json');
  const entries = manifests.get(manifestPath) ?? {};
  entries[path.basename(outPath)] = hash;
  manifests.set(manifestPath, entries);
}

function writeOrCheckFile(outPath, canonical, hash, source) {
  if (check) {
    const existing = fs.existsSync(outPath) ? fs.readFileSync(outPath, 'utf8') : null;
    if (existing !== canonical) {
      errors.push(`Canonical mismatch: ${outPath} (source ${source})`);
    }
    const shaPath = `${outPath}.sha256`;
    const existingSha = fs.existsSync(shaPath) ? fs.readFileSync(shaPath, 'utf8').trim() : null;
    if (existingSha !== hash) {
      errors.push(`SHA mismatch: ${shaPath} (expected ${hash})`);
    }
  } else {
    fs.mkdirSync(path.dirname(outPath), { recursive: true });
    fs.writeFileSync(outPath, canonical, 'utf8');
    fs.writeFileSync(`${outPath}.sha256`, `${hash}\n`, 'utf8');
    console.log(`Wrote ${outPath} (${hash.slice(0, 12)}…)`);
  }
  registerManifest(outPath, hash);
}

function finaliseManifests() {
  for (const [manifestPath, entries] of manifests.entries()) {
    const sorted = Object.fromEntries(Object.keys(entries).sort().map((k) => [k, entries[k]]));
    const payload = `${JSON.stringify(sorted, null, 2)}\n`;
    if (check) {
      const existing = fs.existsSync(manifestPath) ? fs.readFileSync(manifestPath, 'utf8') : null;
      if (existing !== payload) {
        errors.push(`Manifest mismatch: ${manifestPath}`);
      }
    } else {
      fs.writeFileSync(manifestPath, payload, 'utf8');
    }
  }
}

function detectPipelineRef(meta, file) {
  if (meta && typeof meta.pipelineRef === 'string' && meta.pipelineRef.length > 0) {
    return meta.pipelineRef;
  }
  errors.push(`Missing meta.pipelineRef in ${file}`);
  return null;
}

function buildMonitorBundle(raw, file) {
  const pipelineRef = detectPipelineRef(raw.meta ?? {}, file);
  const monitors = Array.isArray(raw.monitors) ? raw.monitors : [];
  if (monitors.length === 0) {
    errors.push(`No monitors defined in ${file}`);
  }
 const canonicalMonitors = monitors.map((monitor) => {
   const id = monitor.monitor_id || monitor.id;
   if (!id) {
     errors.push(`Monitor without id in ${file}`);
   }
    const slug = (id || 'unknown-monitor')
      .toLowerCase()
      .replace(/[^a-z0-9-]+/g, '-')
      .replace(/^-+/, '')
      .replace(/-+$/, '') || 'monitor';
    return {
      id: slug,
      name: id || undefined,
      kind: 'metric',
      select: '*',
      expr: 'true',
      when: 'post',
      actions: ['emit-metric'],
      severity: 'info'
    };
  });
  return {
    schemaVersion: '0.6',
    pipelineRef: pipelineRef || '',
    monitors: canonicalMonitors
  };
}

for (const file of files) {
  const raw = JSON.parse(fs.readFileSync(file, 'utf8'));
  if (Array.isArray(raw.monitors)) {
    const bundle = buildMonitorBundle(raw, file);
    const canonical = stableStringify(bundle);
    const hash = sha256(canonical);
    const baseName = raw.bundle_id
      ? raw.bundle_id.replace(/^monitors\./, '')
      : path.basename(file).replace(/\.l0\.dev\.json$/, '');
    const outPath = path.join(outDir, 'monitors', `${baseName}.l0m.json`);
    writeOrCheckFile(outPath, canonical, hash, file);
    continue;
  }

  if (!raw || typeof raw !== 'object' || (!Array.isArray(raw.nodes) && typeof raw.nodes !== 'object')) {
    errors.push(`Unrecognised artifact shape: ${file}`);
    continue;
  }

  const cleaned = stripExtras(raw);
  const canonical = stableStringify(cleaned);
  const hash = sha256(canonical);

  const pipelineId = cleaned.pipeline_id || raw.pipeline_id;
  const baseName = pipelineId || path.basename(file).replace(/\.l0\.dev\.json$/, '');
  const outPath = path.join(outDir, 'pipelines', `${baseName}.l0.json`);
  writeOrCheckFile(outPath, canonical, hash, file);
}

finaliseManifests();

if (errors.length > 0) {
  console.error('Canonical export errors:');
  for (const err of errors) {
    console.error(` - ${err}`);
  }
  process.exit(1);
}
