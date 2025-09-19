#!/usr/bin/env node
import { cpSync, mkdirSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const pkgDir = resolve(here, '..');
const srcDir = resolve(pkgDir, 'src', 'schema');
const distDir = resolve(pkgDir, 'dist', 'schema');

mkdirSync(distDir, { recursive: true });
cpSync(srcDir, distDir, { recursive: true });
console.log(`[tf-plan-core] Copied schema from ${srcDir} to ${distDir}`);

