#!/usr/bin/env node
import { promises as fs } from 'node:fs';
import path from 'node:path';
import { discoverTests } from './common.mjs';

const root = process.cwd();
const outDir = path.join(root, 'out', '0.4', 'tests');
const outFile = path.join(outDir, 'available.json');

const tests = await discoverTests({ root });

const manifest = {
  tests: tests.map(test => ({
    file: test.file,
    kind: test.kind,
    area: test.area,
    speed: test.speed,
    deps: test.deps,
    runner: test.runner,
  })),
};

await fs.mkdir(outDir, { recursive: true });
await fs.writeFile(outFile, JSON.stringify(manifest, null, 2) + '\n');
