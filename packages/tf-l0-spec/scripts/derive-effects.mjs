import { readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { canonicalize } from './canonical-json.mjs';

const spec = 'packages/tf-l0-spec/spec';
const rules = JSON.parse(await readFile('packages/tf-l0-spec/rules/effect-rules.json', 'utf8')).rules;

function derive(name) {
  const n = name.toLowerCase();
  const out = new Set();
  for (const r of rules) if (new RegExp(r.match).test(n)) for (const e of r.effects) out.add(e);
  return Array.from(out);
}

const catalog = JSON.parse(await readFile(join(spec, 'catalog.json'), 'utf8'));
for (const p of catalog.primitives) {
  if (!Array.isArray(p.effects) || p.effects.length === 0) {
    p.effects = derive(p.name);
  }
}
await writeFile(join(spec, 'effects.json'), canonicalize({
  catalog_semver: catalog.catalog_semver,
  effects: catalog.primitives.map(p => ({ id: p.id, effects: p.effects }))
}) + '\n', 'utf8');

await writeFile(join(spec, 'catalog.json'), canonicalize(catalog) + '\n', 'utf8');
console.log("effects derived and catalog.json updated.");
