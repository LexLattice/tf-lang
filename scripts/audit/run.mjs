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

function accumulateSummary(schemas, determinism, links, catalog) {
  let errors = 0;
  let warnings = 0;

  const schemaFailures = schemas.entries.filter((entry) => !entry.ok).length;
  errors += schemaFailures;

  const brokenLinks = links.broken.length;
  errors += brokenLinks;

  for (const issue of determinism.issues) {
    if (issue.issue === 'has_crlf') {
      errors += 1;
    } else if (issue.issue === 'missing_exec') {
      if (issue.workflow) {
        errors += 1;
      } else {
        warnings += 1;
      }
    } else if (issue.issue === 'missing_shebang') {
      if (issue.workflow) {
        errors += 1;
      } else {
        warnings += 1;
      }
    } else if (issue.issue === 'missing_newline') {
      warnings += 1;
    }
  }

  errors += catalog.prims_missing_effects.length;
  warnings += catalog.effects_unrecognized.length;
  errors += catalog.laws_ref_missing_prims.length;

  return { errors, warnings };
}

export async function run() {
  const schemas = await checkSchemas();
  const determinism = await checkDeterminism();
  const links = await checkLinks();
  const catalog = await checkCatalog();

  const summary = accumulateSummary(schemas, determinism, links, catalog);
  const ok = summary.errors === 0;

  const report = { ok, schemas, determinism, links, catalog, summary };

  await mkdir(REPORT_DIR, { recursive: true });
  await writeFile(REPORT_PATH, `${JSON.stringify(report, null, 2)}\n`, 'utf8');

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
  await run();
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
