#!/usr/bin/env node
// scripts/validate-trace.mjs
import fs from 'node:fs';
import { readFileSync } from 'node:fs';
import readline from 'node:readline';
import path from 'node:path';
import url from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';

const __dirname = path.dirname(url.fileURLToPath(import.meta.url));
const schemaPath = path.resolve(__dirname, '../schemas/trace.v0.4.schema.json');

const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
const ajv = new Ajv2020({ allErrors: true, strict: true });
const validate = ajv.compile(schema);

const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });

let lineNo = 0;
let ok = true;

const errors = [];

for await (const line of rl) {
  lineNo++;
  const trimmed = line.trim();
  if (!trimmed) continue; // allow blank lines
  let obj;
  try {
    obj = JSON.parse(trimmed);
  } catch (e) {
    ok = false;
    errors.push({ line: lineNo, error: `invalid JSON: ${e.message}` });
    continue;
  }
  const valid = validate(obj);
  if (!valid) {
    ok = false;
    errors.push({ line: lineNo, error: ajv.errorsText(validate.errors, { separator: '; ' }) });
  }
}

if (!ok) {
  console.error(JSON.stringify({ ok, errors }, null, 2));
  process.exit(1);
} else {
  console.log(JSON.stringify({ ok: true, lines: lineNo }));
}
