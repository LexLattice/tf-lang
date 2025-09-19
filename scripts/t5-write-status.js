#!/usr/bin/env node
const { createHash } = require('node:crypto');
const { readFileSync, writeFileSync, mkdirSync } = require('node:fs');
const { join } = require('node:path');

const ROOT = process.cwd();
const OUTPUT_DIR = join(ROOT, 'out', 't5');

const TARGETS = [
  { key: 'frames.ndjson', relativePath: join('out', 't5', 'replay', 'frames.ndjson') },
  { key: 'orders.ndjson', relativePath: join('out', 't5', 'effects', 'orders.ndjson') },
  { key: 'evaluations.ndjson', relativePath: join('out', 't5', 'risk', 'evaluations.ndjson') },
];

function computeFileStats(path) {
  const buffer = readFileSync(path);
  const text = buffer.toString('utf-8');
  const trimmed = text.trim();
  const lines = trimmed.length === 0 ? 0 : trimmed.split(/\r?\n/).length;
  const sha256 = createHash('sha256').update(buffer).digest('hex');
  return { lines, sha256 };
}

const status = {
  seed: 42,
  slice: '0:50:1',
  files: {},
};

for (const target of TARGETS) {
  const absolute = join(ROOT, target.relativePath);
  status.files[target.key] = computeFileStats(absolute);
}

mkdirSync(OUTPUT_DIR, { recursive: true });
const statusPath = join(OUTPUT_DIR, 'status.json');
writeFileSync(statusPath, JSON.stringify(status, null, 2) + '\n');
console.log(JSON.stringify(status, null, 2));
