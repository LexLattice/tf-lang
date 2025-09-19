#!/usr/bin/env node
import { cpSync, mkdirSync, readdirSync, statSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const srcDir = resolve(here, '..', 'src', 'schemas');
const distDir = resolve(here, '..', 'dist', 'schemas');

mkdirSync(distDir, { recursive: true });

for (const entry of readdirSync(srcDir)) {
  const absolute = join(srcDir, entry);
  if (statSync(absolute).isFile() && entry.endsWith('.json')) {
    const target = join(distDir, entry);
    cpSync(absolute, target);
  }
}
