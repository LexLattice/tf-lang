#!/usr/bin/env node
const { createHash } = require('node:crypto');
const { readFileSync, writeFileSync, mkdirSync } = require('node:fs');
const { dirname } = require('node:path');

const targets = [
  { key: 'frames.ndjson', path: 'out/t5/replay/frames.ndjson' },
  { key: 'orders.ndjson', path: 'out/t5/effects/orders.ndjson' },
  { key: 'evaluations.ndjson', path: 'out/t5/risk/evaluations.ndjson' },
];

const status = {
  seed: 42,
  slice: '0:50:1',
  files: {},
};

for (const target of targets) {
  const content = readFileSync(target.path);
  const hash = createHash('sha256').update(content).digest('hex');
  const text = content.toString('utf-8');
  const lineCount = text.split(/\n/).filter((line) => line.trim().length > 0).length;
  status.files[target.key] = { lines: lineCount, sha256: hash };
}

const statusPath = 'out/t5/status.json';
mkdirSync(dirname(statusPath), { recursive: true });
writeFileSync(statusPath, JSON.stringify(status, null, 2) + '\n');

console.log(JSON.stringify(status, null, 2));
