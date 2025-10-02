#!/usr/bin/env node
import fs from 'node:fs';
import { execSync } from 'node:child_process';

const out = execSync("git ls-files -- ':(glob)examples/**/monitors/*.l0m.json'", { encoding: 'utf8' }).trim();
const files = out ? out.split(/\r?\n/).filter(Boolean) : [];

const seen = new Map();
let failed = false;

for (const file of files) {
  const bundle = JSON.parse(fs.readFileSync(file, 'utf8'));
  for (const monitor of bundle.monitors || []) {
    const id = monitor?.id;
    if (!id) continue;
    if (seen.has(id)) {
      console.error(`Duplicate monitor id '${id}': ${seen.get(id)} and ${file}`);
      failed = true;
    } else {
      seen.set(id, file);
    }
  }
}

if (failed) process.exit(1);
if (files.length) {
  console.log(`Verified monitor id uniqueness across ${files.length} bundle(s).`);
} else {
  console.log('No monitor bundles found for id check.');
}
