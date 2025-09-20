/* Build ids.json from YAML catalogs (deterministic).
 * Accepts both .yaml and .yml and prints basic diagnostics.
 */
import { readFile, readdir, writeFile, stat } from 'node:fs/promises';
import { join } from 'node:path';
import YAML from 'yaml';

const CATALOG_DIR = 'catalogs';
const SPEC_DIR = 'packages/tf-l0-spec/spec';

const domainMap = (name) => ({
  'frontend_primitives.yaml': 'frontend',
  'frontend_primitives.yml': 'frontend',
  'information_primitives.yaml': 'information',
  'information_primitives.yml': 'information',
  'interaction_interface.yaml': 'interaction',
  'interaction_interface.yml': 'interaction',
  'observability_telemetry.yaml': 'observability',
  'observability_telemetry.yml': 'observability',
  'policy_governance.yaml': 'policy',
  'policy_governance.yml': 'policy',
  'process_computation.yaml': 'process',
  'process_computation.yml': 'process',
  'resource_infrastructure.yaml': 'resource',
  'resource_infrastructure.yml': 'resource',
  'security_primitives.yaml': 'security',
  'security_primitives.yml': 'security',
  'state_identity.yaml': 'state',
  'state_identity.yml': 'state'
}[name] || 'misc');

function slug(s) {
  return String(s).trim().replace(/[^A-Za-z0-9]+/g, '-').replace(/^-+|-+$/g, '').toLowerCase();
}

function* walk(node) {
  if (node && typeof node === 'object') {
    if (Array.isArray(node)) {
      for (const it of node) yield* walk(it);
    } else {
      yield node;
      for (const v of Object.values(node)) yield* walk(v);
    }
  }
}

async function collect(file) {
  const txt = await readFile(join(CATALOG_DIR, file), 'utf8');
  const docs = YAML.parseAllDocuments(txt).map(d => d.toJSON());
  const domain = domainMap(file);
  const out = [];
  for (const doc of docs) {
    for (const obj of walk(doc)) {
      const name = obj?.name || obj?.op || obj?.operation || obj?.primitive || obj?.title;
      const hasIO = obj && typeof obj === 'object' &&
        (('inputs' in obj) || ('outputs' in obj) || ('effect' in obj) || ('effects' in obj));
      if (typeof name === 'string' && hasIO) {
        out.push({ domain, name: slug(name), source: file });
      }
    }
  }
  return out;
}

function canonicalize(value) {
  return JSON.stringify(sortKeys(value));
}
function sortKeys(v) {
  if (v === null || typeof v !== 'object') return v;
  if (Array.isArray(v)) return v.map(sortKeys);
  const out = {};
  for (const k of Object.keys(v).sort()) out[k] = sortKeys(v[k]);
  return out;
}

try {
  await stat(CATALOG_DIR);
} catch {
  console.error(`[A0] catalogs dir not found: ${CATALOG_DIR}. Put your YAMLs there.`);
}

const all = (await readdir(CATALOG_DIR).catch(() => [])).sort();
const files = all.filter(f => f.endsWith('.yaml') || f.endsWith('.yml'));
if (files.length === 0) {
  console.warn(`[A0] No .yaml/.yml files found in ${CATALOG_DIR}. ids.json will be empty.`);
}

const map = new Map();
for (const f of files) {
  const items = await collect(f);
  for (const item of items) {
    const key = item.domain + '|' + item.name;
    if (!map.has(key)) {
      map.set(key, {
        id: `tf:${item.domain}/${item.name}@1`,
        domain: item.domain,
        name: item.name,
        major: 1,
        sources: [f]
      });
    } else {
      const cur = map.get(key);
      if (!cur.sources.includes(f)) cur.sources.push(f);
    }
  }
}

const ids = Array.from(map.values()).sort((a, b) => a.id.localeCompare(b.id));
const payload = { id_policy: 'tf:<domain>/<name>@<major>', catalog_semver: '0.4.0-alpha.0', primitives: ids };
await writeFile(join(SPEC_DIR, 'ids.json'), canonicalize(payload) + '\n', 'utf8');
console.log(`ids.json with ${ids.length} entries written.`);
