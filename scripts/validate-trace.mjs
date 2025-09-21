#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { createInterface } from 'node:readline';
import { stdin, stdout } from 'node:process';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import Ajv from 'ajv/dist/2020.js';

async function loadSchema() {
  const here = path.dirname(fileURLToPath(import.meta.url));
  const schemaPath = path.join(here, '../schemas/trace.v0.4.schema.json');
  const raw = await readFile(schemaPath, 'utf8');
  return JSON.parse(raw);
}

function formatError(error) {
  if (!error) return 'Unknown validation error';
  if (error.keyword === 'required' && typeof error.params?.missingProperty === 'string') {
    return `${error.params.missingProperty} is required`;
  }
  const pathSegment = error.instancePath
    ? error.instancePath.replace(/\//g, '.').replace(/^\./, '')
    : '';
  if (pathSegment) {
    if (error.message) return `${pathSegment} ${error.message}`;
    return `${pathSegment} ${error.keyword} validation failed`;
  }
  if (error.message) return error.message;
  return `${error.keyword ?? 'schema'} validation failed`;
}

async function main() {
  stdin.setEncoding('utf8');
  const schema = await loadSchema();
  const ajv = new Ajv({ strict: false, allErrors: true });
  const validate = ajv.compile(schema);

  const rl = createInterface({ input: stdin, crlfDelay: Infinity });

  let total = 0;
  let invalid = 0;
  const examples = [];
  let lineNo = 0;

  for await (const line of rl) {
    lineNo += 1;
    if (!line.trim()) {
      continue;
    }
    total += 1;
    let record;
    try {
      record = JSON.parse(line);
    } catch (err) {
      invalid += 1;
      if (examples.length < 3) {
        examples.push({ line: lineNo, error: err instanceof Error ? err.message : 'Invalid JSON' });
      }
      continue;
    }

    const ok = validate(record);
    if (!ok) {
      invalid += 1;
      if (examples.length < 3) {
        const message = formatError(validate.errors?.[0]);
        examples.push({ line: lineNo, error: message });
      }
    }
  }

  const summary = invalid === 0
    ? { ok: true, total, invalid: 0 }
    : { ok: false, total, invalid, examples };

  stdout.write(`${JSON.stringify(summary)}\n`);
  if (invalid > 0) {
    process.exitCode = 1;
  }
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
