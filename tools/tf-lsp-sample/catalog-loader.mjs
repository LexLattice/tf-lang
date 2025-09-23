import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));

export async function loadSampleCatalog() {
  const catalogPath = join(here, '../../packages/tf-l0-spec/spec/catalog.json');
  const raw = await readFile(catalogPath, 'utf8');
  return JSON.parse(raw);
}
