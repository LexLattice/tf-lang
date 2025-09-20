import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { join } from 'node:path';
import { createHash } from 'node:crypto';

const spec = 'packages/tf-l0-spec/spec';
const outDir = 'out/0.4';
await mkdir(outDir, { recursive: true });

const cat = await readFile(join(spec, 'catalog.json'));
const ch = 'sha256:' + createHash('sha256').update(cat).digest('hex');
await writeFile(join(spec, 'catalog-hash.txt'), ch + '\n', 'utf8');

const status = {
  sprint: "A1",
  done: ["spec/catalog.json","spec/effects.json","spec/laws.json","spec/catalog-hash.txt"],
  partial: [],
  todo: [],
  hashes: {"spec/catalog.json": ch},
  inputs: { ids: "spec/ids.json" },
  notes: "A1 groundwork complete (skeletons)"
};
await writeFile(join(outDir, 'status.json'), JSON.stringify(status, null, 2) + '\n', 'utf8');
console.log("A1 finalize complete.");
