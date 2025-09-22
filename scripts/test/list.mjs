import { mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { discoverTests } from './discover.mjs';

const ROOT = path.resolve(fileURLToPath(new URL('../../', import.meta.url)));
const OUT_DIR = path.join(ROOT, 'out', '0.4', 'tests');

async function main() {
  const tests = await discoverTests();
  await mkdir(OUT_DIR, { recursive: true });
  const manifest = {
    tests: tests.map((test) => ({
      file: test.file,
      kind: test.kind,
      area: test.area,
      speed: test.speed,
      deps: test.deps,
      runner: test.runner.type,
    })),
  };
  const target = path.join(OUT_DIR, 'available.json');
  const json = JSON.stringify(manifest, null, 2) + '\n';
  await writeFile(target, json, 'utf8');
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
