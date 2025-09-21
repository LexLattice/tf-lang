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
const expectedIr = typeof values.ir === 'string' ? values.ir : null;
const expectedManifest = typeof values.manifest === 'string' ? values.manifest : null;
const expectedCatalog = typeof values.catalog === 'string' ? values.catalog : null;
const expectMeta = Boolean(requireMeta || expectedIr || expectedManifest || expectedCatalog);

const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });

let lineNo = 0;
let total = 0;
let invalid = 0;
const errors = [];

for await (const line of rl) {
  lineNo++;
  const trimmed = line.trim();
  if (!trimmed) continue;
  total++;

  let obj;
  try {
    obj = JSON.parse(trimmed);
  } catch (err) {
    invalid += 1;
    errors.push({ line: lineNo, error: `invalid JSON: ${err.message}` });
    continue;
  }

  if (!validate(obj)) {
    invalid += 1;
    errors.push({ line: lineNo, error: ajv.errorsText(validate.errors, { separator: '; ' }) });
    continue;
  }

  const meta = obj.meta;
  if (expectMeta && (!meta || typeof meta !== 'object')) {
    invalid += 1;
    errors.push({ line: lineNo, error: 'missing meta object' });
    continue;
  }

  if (meta && typeof meta === 'object') {
    let mismatch = false;
    if (expectedIr) {
      const actual = typeof meta.ir_hash === 'string' ? meta.ir_hash : '';
      if (actual !== expectedIr) {
        mismatch = true;
        errors.push({
          line: lineNo,
          error: `meta.ir_hash mismatch (expected ${expectedIr}, got ${actual || '""'})`,
        });
      }
    }
    if (expectedManifest) {
      const actual = typeof meta.manifest_hash === 'string' ? meta.manifest_hash : '';
      if (actual !== expectedManifest) {
        mismatch = true;
        errors.push({
          line: lineNo,
          error: `meta.manifest_hash mismatch (expected ${expectedManifest}, got ${actual || '""'})`,
        });
      }
    }
    if (expectedCatalog) {
      const actual = typeof meta.catalog_hash === 'string' ? meta.catalog_hash : '';
      if (actual !== expectedCatalog) {
        mismatch = true;
        errors.push({
          line: lineNo,
          error: `meta.catalog_hash mismatch (expected ${expectedCatalog}, got ${actual || '""'})`,
        });
      }
    }
    if (mismatch) {
      invalid += 1;
    }
  }
}

const ok = invalid === 0;
const summary = {
  ok,
  total,
  invalid,
  meta_checked: expectMeta,
};

if (!ok) {
  summary.errors = errors;
  console.error(JSON.stringify(summary, null, 2));
  process.exit(1);
} else {
  process.stdout.write(JSON.stringify(summary) + '\n');
}
