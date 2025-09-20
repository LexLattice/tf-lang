import { readFile, readdir, writeFile } from 'node:fs/promises';
import { join, basename } from 'node:path';
import YAML from 'yaml';
import { canonicalize } from './canonical-json.mjs';

const CATALOG_DIR = 'catalogs';
const SPEC_DIR = 'packages/tf-l0-spec/spec';

const domainMap = (name) => ({
  'frontend_primitives.yaml': 'frontend',
  'information_primitives.yaml': 'information',
  'interaction_interface.yaml': 'interaction',
  'observability_telemetry.yaml': 'observability',
  'policy_governance.yaml': 'policy',
  'process_computation.yaml': 'process',
  'resource_infrastructure.yaml': 'resource',
  'security_primitives.yaml': 'security',
  'state_identity.yaml': 'state',
})[name] || 'misc';

function slug(s) {
  return String(s).trim().replace(/[^A-Za-z0-9]+/g, '-').replace(/^-+|-+$/g, '').toLowerCase();
}

function* walk(node) {
  if (node && typeof node === 'object') {
    if (Array.isArray(node)) { for (const it of node) yield* walk(it); }
    else { yield node; for (const v of Object.values(node)) yield* walk(v); }
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
      const hasIO = obj && typeof obj === 'object' && (('inputs' in obj) || ('outputs' in obj) || ('effect' in obj) || ('effects' in obj));
      if (typeof name === 'string' && hasIO) out.push({ domain, name: slug(name), source: file });
    }
  }
  return out;
}

const files = (await readdir(CATALOG_DIR)).filter(f => f.endsWith('.yaml')).sort();
const map = new Map();
for (const f of files) {
  for await (const item of collect(f)) {
    const key = item.domain + '|' + item.name;
    if (!map.has(key)) map.set(key, { id: `tf:${item.domain}/${item.name}@1`, domain: item.domain, name: item.name, major: 1, sources: [f] });
    else { const cur = map.get(key); if (!cur.sources.includes(f)) cur.sources.push(f); }
  }
}
const ids = Array.from(map.values()).sort((a,b)=>a.id.localeCompare(b.id));
const payload = { id_policy: "tf:<domain>/<name>@<major>", catalog_semver: "0.4.0-alpha.0", primitives: ids };
await writeFile(join(SPEC_DIR, 'ids.json'), canonicalize(payload) + '\n', 'utf8');
console.log(`ids.json with ${ids.length} entries written.`);
