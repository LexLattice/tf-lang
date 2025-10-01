#!/usr/bin/env node
// tools/link-checker.mjs
import path from 'node:path';
import { pathToFileURL } from 'node:url';

async function loadAuditChecker() {
  const url = pathToFileURL(path.join(process.cwd(), 'scripts/audit/check-links.mjs')).href;
  const module = await import(url);
  if (!module.run || typeof module.run !== 'function') {
    throw new Error('scripts/audit/check-links.mjs does not export run()');
  }
  return module.run;
}

function normalizeFilter(entry) {
  const trimmed = entry.trim().replace(/\\/g, '/');
  if (trimmed === '' || trimmed === '.') {
    return '';
  }
  return trimmed.replace(/\/+$|\.$/g, '');
}

function matchesFilter(entryFrom, filters) {
  if (filters.length === 0) {
    return true;
  }
  return filters.some((filter) => {
    if (filter === '') {
      return true;
    }
    if (entryFrom === filter) {
      return true;
    }
    return entryFrom.startsWith(`${filter}/`);
  });
}

async function main() {
  const run = await loadAuditChecker();
  const { ok, broken } = await run();
  const filters = process.argv.slice(2).map(normalizeFilter).filter((entry) => entry.length > 0);
  const filtered = broken.filter((entry) => matchesFilter(entry.from, filters));
  const result = {
    ok: filtered.length === 0,
    broken: filtered,
    filters,
  };
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  if (!result.ok) {
    process.exitCode = 1;
  }
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  main().catch((err) => {
    process.stderr.write(`tools/link-checker failed: ${err?.stack || err}\n`);
    process.exitCode = 1;
  });
}
