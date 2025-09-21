#!/usr/bin/env node

import { writeFile, mkdir } from 'node:fs/promises';
import { dirname, join } from 'node:path';
import { checkSchemas } from './check-schemas.mjs';
import { checkDeterminism } from './check-determinism.mjs';
import { checkLinks } from './check-links.mjs';
import { checkCatalog } from './check-catalog.mjs';

const REPORT_PATH = 'out/0.4/audit/report.json';

async function main() {
  const [schemas, determinism, links, catalog] = await Promise.all([
    checkSchemas(),
    checkDeterminism(),
    checkLinks(),
    checkCatalog(),
  ]);

  let ok = true;
  let errors = 0;
  let warnings = 0;

  // P1: schema compile failure
  if (schemas.some(s => !s.ok)) {
    ok = false;
    errors += schemas.filter(s => !s.ok).length;
  }

  // P1: broken relative doc link
  if (links.broken.length > 0) {
    ok = false;
    errors += links.broken.length;
  }

  // P1: missing exec bit, CRLF detected
  const determinismErrors = determinism.filter(d => d.issue === 'missing_exec' || d.issue === 'has_crlf');
  if (determinismErrors.length > 0) {
    ok = false;
    errors += determinismErrors.length;
  }

  const determinismWarnings = determinism.filter(d => d.issue !== 'missing_exec' && d.issue !== 'has_crlf');
  warnings += determinismWarnings.length;


  // P1: primitive with no effects[]
  if (catalog.prims_missing_effects.length > 0) {
    ok = false;
    errors += catalog.prims_missing_effects.length;
  }

  warnings += catalog.effects_unrecognized.length;
  warnings += catalog.laws_ref_missing_prims.length;


  const report = {
    ok,
    schemas: {
        results: schemas,
        summary: {
            pass: schemas.filter(s => s.ok).length,
            fail: schemas.filter(s => !s.ok).length,
        }
    },
    determinism: {
        results: determinism,
        summary: {
            errors: determinismErrors.length,
            warnings: determinismWarnings.length,
        }
    },
    links: {
        results: links,
        summary: {
            broken: links.broken.length,
        }
    },
    catalog: {
        results: catalog,
        summary: {
            errors: catalog.prims_missing_effects.length,
            warnings: catalog.effects_unrecognized.length + catalog.laws_ref_missing_prims.length,
        }
    },
    summary: {
      errors,
      warnings,
    },
  };

  await mkdir(dirname(REPORT_PATH), { recursive: true });
  await writeFile(REPORT_PATH, JSON.stringify(report, null, 2) + '\n');

  console.log(`Audit report written to ${REPORT_PATH}`);
  if (!ok) {
    console.error('Audit failed with P1 issues.');
    process.exit(1);
  }
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
