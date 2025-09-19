#!/usr/bin/env node
const { createHash } = require('node:crypto');
const { readFileSync, writeFileSync, mkdirSync } = require('node:fs');
const { dirname, join } = require('node:path');

function main() {
  const root = process.cwd();
  const targets = {
    'frames.ndjson': join(root, 'out', 't5', 'replay', 'frames.ndjson'),
    'orders.ndjson': join(root, 'out', 't5', 'effects', 'orders.ndjson'),
    'evaluations.ndjson': join(root, 'out', 't5', 'risk', 'evaluations.ndjson'),
  };

  const files = {};
  for (const [name, path] of Object.entries(targets)) {
    const content = readFileSync(path, 'utf-8');
    const hash = createHash('sha256');
    hash.update(content);
    const lines = content.split(/\n/).filter((line) => line.length > 0).length;
    files[name] = { lines, sha256: hash.digest('hex') };
  }

  const status = {
    seed: 42,
    slice: '0:50:1',
    files,
  };

  const outPath = join(root, 'out', 't5', 'status.json');
  mkdirSync(dirname(outPath), { recursive: true });
  writeFileSync(outPath, JSON.stringify(status, null, 2) + '\n');
}

main();
