import { readFile } from 'node:fs/promises';
export async function loadCatalog() {
  const candidates = [
    'packages/tf-l0-spec/spec/catalog.json',
    'catalogs/catalog.json',
  ];
  for (const p of candidates) {
    try { return JSON.parse(await readFile(p, 'utf8')); } catch { }
  }
  return { primitives: [] };
}
