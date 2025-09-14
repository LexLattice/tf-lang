#!/usr/bin/env -S node --loader tsx
// Simple JSON fixtures sanity check: verify parsable JSON files in common dirs.
import { promises as fs } from 'fs';
import { join } from 'path';

async function* walk(dir: string): AsyncGenerator<string> {
  const ents = await fs.readdir(dir, { withFileTypes: true });
  for (const e of ents) {
    const p = join(dir, e.name);
    if (e.isDirectory()) yield* walk(p);
    else yield p;
  }
}

async function main() {
  const roots = [
    'tests/vectors',
    'docs/data',
    'tests',
  ];
  const jsonFiles: string[] = [];
  for (const r of roots) {
    try {
      for await (const p of walk(r)) if (p.endsWith('.json')) jsonFiles.push(p);
    } catch (_e) {
      // directory missing is ok
    }
  }
  let bad = 0;
  for (const p of jsonFiles) {
    try {
      const txt = await fs.readFile(p, 'utf8');
      JSON.parse(txt);
      process.stdout.write(`ok  ${p}\n`);
    } catch (e) {
      bad++;
      process.stderr.write(`FAIL ${p}: ${(e as Error).message}\n`);
    }
  }
  if (bad) {
    throw new Error(`Invalid JSON in ${bad} file(s)`);
  }
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});

