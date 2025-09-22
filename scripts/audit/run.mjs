#!/usr/bin/env node
// scripts/audit/run.mjs
import { mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { run as checkSchemas } from './check-schemas.mjs';
import { run as checkDeterminism } from './check-determinism.mjs';
import { run as checkLinks } from './check-links.mjs';
import { run as checkCatalog } from './check-catalog.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');
const REPORT_DIR = path.join(ROOT, 'out/0.4/audit');
const REPORT_PATH = path.join(REPORT_DIR, 'report.json');
const ARGS = process.argv.slice(2);
const STRICT = ARGS.includes('--strict') || process.env.AUDIT_STRICT === '1';

function sortStrings(values) {
  return Array.isArray(values) ? [...values].map((value) => String(value)).sort((a, b) => a.localeCompare(b)) : [];
}

function canonicalizeSchemas(schemas) {
  const entries = Array.isArray(schemas?.entries) ? schemas.entries : [];
  const normalized = entries.map((entry) => {
    const file = typeof entry?.file === 'string' ? entry.file : String(entry?.file || '');
    const base = { file, ok: Boolean(entry?.ok) };
    if (Array.isArray(entry?.errors) && entry.errors.length > 0) {
      base.errors = sortStrings(entry.errors);
    }
    return base;
  });
  normalized.sort((a, b) => a.file.localeCompare(b.file));
  return {
    ok: Boolean(schemas?.ok),
    entries: normalized,
  };
}

function canonicalizeDeterminism(determinism) {
  const issues = Array.isArray(determinism?.issues) ? determinism.issues : [];
  const normalized = issues.map((issue) => {
    const entry = {
      path: typeof issue?.path === 'string' ? issue.path : String(issue?.path || ''),
      issue: typeof issue?.issue === 'string' ? issue.issue : String(issue?.issue || ''),
    };
    if (issue?.workflow) {
      entry.workflow = true;
    }
    if (issue?.error) {
      entry.error = String(issue.error);
    }
    return entry;
  });
  normalized.sort((a, b) => {
    if (a.path === b.path) {
      return a.issue.localeCompare(b.issue);
    }
    return a.path.localeCompare(b.path);
  });
  return {
    ok: Boolean(determinism?.ok),
    issues: normalized,
  };
}

function canonicalizeLinks(links) {
  const broken = Array.isArray(links?.broken) ? links.broken : [];
  const normalized = broken.map((entry) => ({
    from: typeof entry?.from === 'string' ? entry.from : String(entry?.from || ''),
    href: typeof entry?.href === 'string' ? entry.href : String(entry?.href || ''),
  }));
  normalized.sort((a, b) => {
    if (a.from === b.from) {
      return a.href.localeCompare(b.href);
    }
    return a.from.localeCompare(b.from);
  });
  return {
    ok: Boolean(links?.ok),
    broken: normalized,
  };
}

function canonicalizeCatalog(catalog) {
  return {
    ok: Boolean(catalog?.ok),
    effects_unrecognized: sortStrings(catalog?.effects_unrecognized),
    prims_missing_effects: sortStrings(catalog?.prims_missing_effects),
    laws_ref_missing_prims: sortStrings(catalog?.laws_ref_missing_prims),
  };
}

function accumulateSummary(schemas, determinism, links, catalog) {
  let errors = 0;
  let warnings = 0;

  errors += schemas.entries.filter((entry) => !entry.ok).length;
  errors += links.broken.length;

  for (const issue of determinism.issues) {
    if (issue.issue === 'has_crlf') {
      errors += 1;
    } else if (issue.issue === 'missing_exec' && issue.workflow) {
      errors += 1;
    } else {
      warnings += 1;
    }
  }

  errors += catalog.prims_missing_effects.length;
  warnings += catalog.effects_unrecognized.length;
  warnings += catalog.laws_ref_missing_prims.length;

  return { errors, warnings };
}

export async function run() {
  const rawSchemas = await checkSchemas();
  const rawDeterminism = await checkDeterminism();
  const rawLinks = await checkLinks();
  const rawCatalog = await checkCatalog();

  const schemas = canonicalizeSchemas(rawSchemas);
  const determinism = canonicalizeDeterminism(rawDeterminism);
  const links = canonicalizeLinks(rawLinks);
  const catalog = canonicalizeCatalog(rawCatalog);

  const summary = accumulateSummary(schemas, determinism, links, catalog);
  const ok = summary.errors === 0;

  const report = { ok, schemas, determinism, links, catalog, summary };
  const payload = `${JSON.stringify(report, null, 2)}\n`;

  await mkdir(REPORT_DIR, { recursive: true });
  await writeFile(REPORT_PATH, payload, 'utf8');
  process.stdout.write(payload);

  const logLines = [
    '=== Audit Summary ===',
    `ok: ${ok}`,
    `errors: ${summary.errors}`,
    `warnings: ${summary.warnings}`,
    `report: ${path.relative(ROOT, REPORT_PATH)}`
  ];
  for (const line of logLines) {
    process.stdout.write(`${line}\n`);
  }

  return { report, path: REPORT_PATH };
}

async function main() {
  const { report } = await run();
  if (STRICT && !report.ok) {
    process.exitCode = 1;
  }
}

const isCli = process.argv[1]
  ? pathToFileURL(process.argv[1]).href === import.meta.url
  : false;

if (isCli) {
  main().catch((err) => {
    process.stderr.write(`audit:run failed: ${err?.stack || err}\n`);
    process.exitCode = 1;
  });
}
