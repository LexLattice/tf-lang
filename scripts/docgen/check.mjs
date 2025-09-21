#!/usr/bin/env node
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

import { generateCatalogDoc } from './catalog.mjs';
import { generateDSLDoc } from './dsl.mjs';
import { generateEffectsDoc } from './effects.mjs';
import { resolveRepoRoot } from './utils.mjs';

const execFileAsync = promisify(execFile);

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

async function ensureDocsClean() {
  const { stdout } = await execFileAsync('git', ['status', '--porcelain', 'docs']);
  if (stdout.trim().length === 0) {
    return true;
  }
  process.stderr.write('Docs drift detected. Run "pnpm run docs:gen" and commit the results.\n');
  const diff = await execFileAsync('git', ['--no-pager', 'diff', '--', 'docs']);
  process.stderr.write(diff.stdout);
  process.stderr.write(diff.stderr);
  return false;
}

async function main() {
  const repoRoot = resolveRepoRoot(__dirname);
  await generateCatalogDoc({ root: repoRoot });
  await generateDSLDoc({ root: repoRoot });
  await generateEffectsDoc({ root: repoRoot });
  const clean = await ensureDocsClean();
  if (!clean) {
    process.exitCode = 1;
  }
}

main().catch(err => {
  process.stderr.write(`${err?.stack || err?.message || String(err)}\n`);
  process.exitCode = 1;
});
