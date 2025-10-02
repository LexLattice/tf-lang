#!/usr/bin/env node
import fs from 'node:fs';

function sortDeep(value) {
  if (Array.isArray(value)) {
    return value.map(sortDeep);
  }
  if (value && typeof value === 'object') {
    const out = {};
    for (const key of Object.keys(value).sort()) {
      out[key] = sortDeep(value[key]);
    }
    return out;
  }
  return value;
}

const inputPath = process.argv[2];
if (!inputPath) {
  console.error('Usage: canonical-json.mjs <input.json> > <output.json>');
  process.exit(2);
}

const content = fs.readFileSync(inputPath, 'utf8');
const parsed = JSON.parse(content);
const canonical = JSON.stringify(sortDeep(parsed), null, 2);
process.stdout.write(`${canonical}\n`);
