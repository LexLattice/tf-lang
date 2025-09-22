import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { discoverTests } from './discover.mjs';
import { sortTests, writeJsonCanonical } from './utils.mjs';

const ROOT = path.resolve(fileURLToPath(new URL('../../', import.meta.url)));
const OUT_DIR = path.join(ROOT, 'out', '0.4', 'tests');

async function main() {
  const tests = sortTests(await discoverTests());
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
  manifest.tests.sort((a, b) => {
    const file = a.file.localeCompare(b.file);
    if (file !== 0) return file;
    const kind = a.kind.localeCompare(b.kind);
    if (kind !== 0) return kind;
    const area = a.area.localeCompare(b.area);
    if (area !== 0) return area;
    return a.speed.localeCompare(b.speed);
  });
  await writeJsonCanonical(target, manifest);
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
