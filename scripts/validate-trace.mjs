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
    console.error(`Unexpected argument: ${positionals[0]}`);
    process.exitCode = 2;
    return;
  }

  const requireMeta = Boolean(values['require-meta']);
  const expectedIr = typeof values.ir === 'string' ? values.ir : null;
  const expectedManifest = typeof values.manifest === 'string' ? values.manifest : null;
  const expectedCatalog = typeof values.catalog === 'string' ? values.catalog : null;
  const metaChecked = requireMeta || Boolean(expectedIr || expectedManifest || expectedCatalog);

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
      errors.push({ line: lineNo, error: `invalid JSON: ${e.message}` });
      invalid += 1;
      continue;
    }

    const valid = validate(obj);
    if (!valid) {
      errors.push({ line: lineNo, error: ajv.errorsText(validate.errors, { separator: '; ' }) });
      invalid += 1;
      continue;
    }

    const meta = obj?.meta;
    let lineInvalid = false;

    if (requireMeta && (!meta || typeof meta !== 'object')) {
      errors.push({ line: lineNo, error: 'missing meta object' });
      invalid += 1;
      continue;
    }

    if (metaChecked) {
      if (!meta || typeof meta !== 'object') {
        if (expectedIr || expectedManifest || expectedCatalog) {
          errors.push({ line: lineNo, error: 'missing meta object' });
          invalid += 1;
        }
        continue;
      }

      if (expectedIr && meta.ir_hash !== expectedIr) {
        errors.push({ line: lineNo, error: `meta.ir_hash mismatch (expected ${expectedIr}, got ${meta.ir_hash || 'undefined'})` });
        lineInvalid = true;
      }
      if (expectedManifest && meta.manifest_hash !== expectedManifest) {
        errors.push({
          line: lineNo,
          error: `meta.manifest_hash mismatch (expected ${expectedManifest}, got ${meta.manifest_hash || 'undefined'})`,
        });
        lineInvalid = true;
      }
      if (expectedCatalog && meta.catalog_hash !== expectedCatalog) {
        errors.push({
          line: lineNo,
          error: `meta.catalog_hash mismatch (expected ${expectedCatalog}, got ${meta.catalog_hash || 'undefined'})`,
        });
        lineInvalid = true;
      }
    }

    if (lineInvalid) {
      invalid += 1;
    }
  }

  const ok = errors.length === 0;
  const summary = {
    ok,
    total: lineNo,
    invalid,
    meta_checked: metaChecked,
  };
  if (!ok) {
    summary.errors = errors;
  }

  const output = JSON.stringify(summary);
  if (ok) {
    console.log(output);
  } else {
    console.error(output);
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  console.error(err?.message || err);
  process.exitCode = 1;
});
