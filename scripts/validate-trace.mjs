#!/usr/bin/env node
import { createInterface } from 'node:readline';
import { stdin } from 'node:process';
import { readFile } from 'node:fs/promises';
import Ajv from 'ajv/dist/2020.js';

const schema = JSON.parse(await readFile(new URL('../schemas/trace.v0.4.schema.json', import.meta.url), 'utf8'));
const ajv = new Ajv({ strict: true, allErrors: true });
const validate = ajv.compile(schema);

const rl = createInterface({ input: stdin, crlfDelay: Infinity });

let total = 0;
let invalid = 0;
const examples = [];
let lineNumber = 0;

function formatError(err) {
  if (!err) return 'invalid record';
  if (err.keyword === 'required' && err.params?.missingProperty) {
    return `${err.params.missingProperty} is required`;
  }
  if (err.keyword === 'type' && err.params?.type) {
    const path = err.instancePath ? `${err.instancePath} ` : '';
    return `${path}must be ${err.params.type}`.trim();
  }
  if (err.instancePath) {
    return `${err.instancePath} ${err.message}`.trim();
  }
  return err.message || 'invalid record';
}

for await (const rawLine of rl) {
  lineNumber += 1;
  if (rawLine.trim() === '') {
    continue;
  }
  total += 1;
  let parsed;
  try {
    parsed = JSON.parse(rawLine);
  } catch (err) {
    invalid += 1;
    if (examples.length < 3) {
      examples.push({ line: lineNumber, error: `JSON parse error: ${err.message}` });
    }
    continue;
  }
  const ok = validate(parsed);
  if (!ok) {
    invalid += 1;
    if (examples.length < 3 && Array.isArray(validate.errors) && validate.errors.length > 0) {
      const err = validate.errors[0];
      examples.push({ line: lineNumber, error: formatError(err) });
    } else if (examples.length < 3) {
      examples.push({ line: lineNumber, error: 'invalid record' });
    }
  }
}

const summary = invalid === 0
  ? { ok: true, total, invalid: 0 }
  : { ok: false, total, invalid, examples };

process.stdout.write(`${JSON.stringify(summary)}\n`);
if (invalid > 0) {
  process.exitCode = 1;
}
