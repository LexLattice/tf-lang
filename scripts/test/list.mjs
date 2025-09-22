import { promises as fs } from 'node:fs';
import path from 'node:path';

import { ROOT, discoverTests } from './utils.mjs';

const tests = await discoverTests();

const serialized = tests.map((test) => {
  const base = {
    file: test.file,
    kind: test.kind,
    area: test.area,
    speed: test.speed,
    deps: test.deps,
    runner: test.runner,
  };
  if (test.metaFile) {
    base.meta = test.metaFile;
  }
  if (test.packageDir) {
    base.package = test.packageDir;
  }
  if (test.testFileInPackage) {
    base.testFileInPackage = test.testFileInPackage;
  }
  if (test.cargoTarget) {
    base.cargoTarget = test.cargoTarget;
  }
  if (test.crateDir) {
    base.crate = test.crateDir;
  }
  return base;
});

const manifest = { tests: serialized };

const outputDir = path.join(ROOT, 'out', '0.4', 'tests');
await fs.mkdir(outputDir, { recursive: true });
const outputPath = path.join(outputDir, 'available.json');
await fs.writeFile(outputPath, `${JSON.stringify(manifest, null, 2)}\n`);
console.log(`Wrote ${path.relative(ROOT, outputPath)} with ${serialized.length} tests`);
