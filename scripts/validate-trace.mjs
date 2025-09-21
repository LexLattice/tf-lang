#!/usr/bin/env node
// scripts/validate-trace.mjs
import { readFileSync } from 'node:fs';
import readline from 'node:readline';
import path from 'node:path';
import url from 'node:url';
import { parseArgs } from 'node:util';
import Ajv2020 from 'ajv/dist/2020.js';

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
  process.stderr.write(`unexpected positional argument: ${positionals[0]}\n`);
  process.exit(2);
}

const requireMeta = Boolean(values['require-meta']);
const expectedIrHash = values.ir;
const expectedManifestHash = values.manifest;
const expectedCatalogHash = values.catalog;
const metaCheck = requireMeta || Boolean(expectedIrHash || expectedManifestHash || expectedCatalogHash);

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

const errors = [];

function ensureMeta(lineNumber, record) {
  if (!metaCheck) return true;
  if (!record || typeof record !== 'object' || Array.isArray(record)) return false;
  if (!record.meta || typeof record.meta !== 'object' || Array.isArray(record.meta)) {
    errors.push({ line: lineNumber, error: 'missing meta' });
    return false;
  }
  return true;
}

function checkHash(lineNumber, meta, key, expected) {
  if (!expected) return true;
  if (!meta || typeof meta !== 'object' || Array.isArray(meta)) {
    errors.push({ line: lineNumber, error: `meta.${key} missing` });
    return false;
  }
  const value = meta[key];
  if (typeof value !== 'string') {
    errors.push({ line: lineNumber, error: `meta.${key} missing` });
    return false;
  }
  if (value !== expected) {
    errors.push({ line: lineNumber, error: `meta.${key} mismatch: expected ${expected} got ${value}` });
    return false;
  }
  return true;
}

for await (const line of rl) {
  lineNo++;
  const trimmed = line.trim();
  if (!trimmed) continue;
  total += 1;
  let obj;
  let validLine = true;
  try {
    obj = JSON.parse(trimmed);
  } catch (e) {
    ok = false;
    validLine = false;
    errors.push({ line: lineNo, error: `invalid JSON: ${e.message}` });
    invalidCount += 1;
    continue;
  }
  const valid = validate(obj);
  if (!valid) {
    ok = false;
    validLine = false;
    errors.push({ line: lineNo, error: ajv.errorsText(validate.errors, { separator: '; ' }) });
  }
  const metaOk = ensureMeta(lineNo, obj);
  if (!metaOk) {
    ok = false;
    validLine = false;
  }
  const meta = metaOk ? obj.meta : null;
  const irOk = metaOk ? checkHash(lineNo, meta, 'ir_hash', expectedIrHash) : true;
  const manifestOk = metaOk ? checkHash(lineNo, meta, 'manifest_hash', expectedManifestHash) : true;
  const catalogOk = metaOk ? checkHash(lineNo, meta, 'catalog_hash', expectedCatalogHash) : true;
  if (!irOk || !manifestOk || !catalogOk) {
    ok = false;
    validLine = false;
  }
  if (!validLine) {
    invalidCount += 1;
  }
}

const summary = {
  ok,
  total,
  invalid: invalidCount,
  meta_checked: metaCheck,
};
if (!ok) {
  summary.errors = errors;
}

const output = canonicalJson(summary) + '\n';

if (!ok) {
  process.stderr.write(output);
  process.exit(1);
} else {
  process.stdout.write(output);
}
