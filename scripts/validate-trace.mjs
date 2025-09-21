#!/usr/bin/env node
// scripts/validate-trace.mjs
import { readFile } from 'node:fs/promises';
import { readFileSync } from 'node:fs';
import readline from 'node:readline';
import path from 'node:path';
import url from 'node:url';
import { parseArgs } from 'node:util';
import Ajv2020 from 'ajv/dist/2020.js';

import { sha256OfCanonicalJson } from '../packages/tf-l0-tools/lib/digest.mjs';

function canonicalJson(value) {
  if (Array.isArray(value)) {
    return '[' + value.map(canonicalJson).join(',') + ']';
  }
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    return '{' + keys.map((key) => `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(',') + '}';
  }
  return JSON.stringify(value);
}

function isShaLiteral(value) {
  return typeof value === 'string' && /^sha256:[0-9a-f]{64}$/i.test(value);
}

async function resolveExpected(value, label) {
  if (!value) return null;
  if (isShaLiteral(value)) return value;
  try {
    const raw = await readFile(value, 'utf8');
    const parsed = JSON.parse(raw);
    return sha256OfCanonicalJson(parsed);
  } catch (err) {
    process.stderr.write(`unable to read ${label} digest: ${err?.message || err}\n`);
    process.exit(2);
    return null;
  }
}

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      'require-meta': { type: 'boolean' },
      ir: { type: 'string' },
      manifest: { type: 'string' },
      catalog: { type: 'string' },
    },
    allowPositionals: true,
  });

  if (positionals.length > 0) {
    process.stderr.write(`unexpected positional argument: ${positionals[0]}\n`);
    process.exit(2);
    return;
  }

  const requireMeta = Boolean(values['require-meta']);
  const expectedIrHash = await resolveExpected(values.ir, 'ir');
  const expectedManifestHash = await resolveExpected(values.manifest, 'manifest');
  const expectedCatalogHash = await resolveExpected(values.catalog, 'catalog');
  const metaCheck =
    requireMeta || Boolean(expectedIrHash || expectedManifestHash || expectedCatalogHash);

  const __dirname = path.dirname(url.fileURLToPath(import.meta.url));
  const schemaPath = path.resolve(__dirname, '../schemas/trace.v0.4.schema.json');
  const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: true });
  const validate = ajv.compile(schema);

  const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });

  let lineNo = 0;
  let ok = true;
  let total = 0;
  let invalidCount = 0;

  const issues = [];

  const maxMismatchSamples = 3;
  let mismatchSamples = 0;

  for await (const rawLine of rl) {
    lineNo += 1;
    const trimmed = rawLine.trim();
    if (!trimmed) {
      continue;
    }
    total += 1;
    let lineInvalid = false;
    let record;
    try {
      record = JSON.parse(trimmed);
    } catch (err) {
      ok = false;
      lineInvalid = true;
      issues.push({ line: lineNo, issue: 'invalid_json', message: err?.message || String(err) });
      invalidCount += 1;
      continue;
    }

    const valid = validate(record);
    if (!valid) {
      ok = false;
      lineInvalid = true;
      const message = ajv.errorsText(validate.errors, { separator: '; ' });
      issues.push({ line: lineNo, issue: 'schema', message });
    }

    if (metaCheck) {
      if (!record || typeof record !== 'object' || Array.isArray(record)) {
        ok = false;
        lineInvalid = true;
        issues.push({ line: lineNo, issue: 'missing_meta' });
      } else if (!record.meta || typeof record.meta !== 'object' || Array.isArray(record.meta)) {
        ok = false;
        lineInvalid = true;
        issues.push({ line: lineNo, issue: 'missing_meta' });
      } else {
        const checks = [
          ['ir_hash', expectedIrHash],
          ['manifest_hash', expectedManifestHash],
          ['catalog_hash', expectedCatalogHash],
        ];
        for (const [field, expected] of checks) {
          if (!expected) continue;
          const value = record.meta[field];
          if (typeof value !== 'string') {
            ok = false;
            lineInvalid = true;
            issues.push({ line: lineNo, issue: 'missing_meta_field', which: field });
            continue;
          }
          if (value !== expected) {
            ok = false;
            lineInvalid = true;
            if (mismatchSamples < maxMismatchSamples) {
              issues.push({ line: lineNo, issue: 'hash_mismatch', which: field });
              mismatchSamples += 1;
            }
          }
        }
      }
    }

    if (lineInvalid) {
      invalidCount += 1;
    }
  }

  const summary = {
    ok,
    total,
    invalid: invalidCount,
    meta_checked: metaCheck,
  };
  if (!ok && issues.length > 0) {
    summary.issues = issues;
  }

  const output = canonicalJson(summary) + '\n';
  process.stdout.write(output);
  if (!ok) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  process.stderr.write(`${err?.message || err}\n`);
  process.exit(2);
});
