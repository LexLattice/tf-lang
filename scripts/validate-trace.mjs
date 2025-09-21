#!/usr/bin/env node
// scripts/validate-trace.mjs
import { readFileSync } from 'node:fs';
import readline from 'node:readline';
import path from 'node:path';
import url from 'node:url';
import { parseArgs } from 'node:util';
import Ajv2020 from 'ajv/dist/2020.js';

const __dirname = path.dirname(url.fileURLToPath(import.meta.url));
const schemaPath = path.resolve(__dirname, '../schemas/trace.v0.4.schema.json');

const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
const ajv = new Ajv2020({ allErrors: true, strict: true });
const validate = ajv.compile(schema);

const { values, positionals } = parseArgs({
  args: process.argv.slice(2),
  options: {
    'require-meta': { type: 'boolean' },
    ir: { type: 'string' },
    manifest: { type: 'string' },
    catalog: { type: 'string' },
  },
  allowPositionals: true,
});

if (positionals.length > 0) {
  console.error(`unexpected positional argument: ${positionals[0]}`);
  process.exit(2);
}

const requireMeta = Boolean(values['require-meta']);
const expectedMeta = {
  ir: typeof values.ir === 'string' && values.ir ? values.ir : null,
  manifest: typeof values.manifest === 'string' && values.manifest ? values.manifest : null,
  catalog: typeof values.catalog === 'string' && values.catalog ? values.catalog : null,
};
const metaCheckEnabled =
  requireMeta || expectedMeta.ir || expectedMeta.manifest || expectedMeta.catalog;

const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });

let lineNo = 0;
let invalid = 0;

const errors = [];

for await (const line of rl) {
  const trimmed = line.trim();
  if (!trimmed) continue; // allow blank lines
  lineNo++;
  let obj;
  try {
    obj = JSON.parse(trimmed);
  } catch (e) {
    invalid += 1;
    errors.push({ line: lineNo, error: `invalid JSON: ${e.message}` });
    continue;
  }
  const valid = validate(obj);
  if (!valid) {
    invalid += 1;
    errors.push({ line: lineNo, error: ajv.errorsText(validate.errors, { separator: '; ' }) });
    continue;
  }
  const meta = obj?.meta;
  const hasMeta = meta && typeof meta === 'object' && !Array.isArray(meta);
  if (requireMeta && !hasMeta) {
    invalid += 1;
    errors.push({ line: lineNo, error: 'meta missing (required)' });
    continue;
  }
  if (!metaCheckEnabled) {
    continue;
  }
  if (!hasMeta) {
    if (expectedMeta.ir || expectedMeta.manifest || expectedMeta.catalog) {
      invalid += 1;
      errors.push({ line: lineNo, error: 'meta missing for provenance verification' });
    }
    continue;
  }
  const mismatches = [];
  if (expectedMeta.ir) {
    const value = typeof meta.ir_hash === 'string' ? meta.ir_hash : null;
    if (value !== expectedMeta.ir) {
      mismatches.push('ir_hash');
    }
  }
  if (expectedMeta.manifest) {
    const value = typeof meta.manifest_hash === 'string' ? meta.manifest_hash : null;
    if (value !== expectedMeta.manifest) {
      mismatches.push('manifest_hash');
    }
  }
  if (expectedMeta.catalog) {
    const value = typeof meta.catalog_hash === 'string' ? meta.catalog_hash : null;
    if (value !== expectedMeta.catalog) {
      mismatches.push('catalog_hash');
    }
  }
  if (mismatches.length > 0) {
    invalid += 1;
    errors.push({ line: lineNo, error: `meta mismatch: ${mismatches.join(', ')}` });
  }
}

if (invalid > 0) {
  const summary = { ok: false, total: lineNo, invalid, errors };
  if (metaCheckEnabled) summary.meta_checked = true;
  console.error(JSON.stringify(summary, null, 2));
  process.exit(1);
} else {
  const summary = { ok: true, total: lineNo, invalid: 0 };
  if (metaCheckEnabled) summary.meta_checked = true;
  console.log(JSON.stringify(summary));
}
