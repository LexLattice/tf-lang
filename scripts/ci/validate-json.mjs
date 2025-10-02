#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import AjvDraft from 'ajv';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

function parseArgs(argv) {
  const patterns = [];
  let schemaPath = null;
  let strict = false;

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--schema') {
      if (i + 1 >= argv.length) {
        console.error('Expected value after --schema');
        process.exit(2);
      }
      schemaPath = argv[++i];
    } else if (arg === '--strict') {
      strict = true;
    } else {
      patterns.push(arg);
    }
  }

  if (!schemaPath) {
    console.error('Usage: validate-json.mjs [--strict] --schema <schema> <glob...>');
    process.exit(2);
  }
  if (patterns.length === 0) {
    console.error('Provide at least one file glob to validate.');
    process.exit(2);
  }
  return { schemaPath, patterns, strict };
}

const { schemaPath, patterns, strict } = parseArgs(process.argv.slice(2));

function expand(pattern) {
  const output = execFileSync('git', ['ls-files', '--', `:(glob)${pattern}`], {
    encoding: 'utf8',
  }).trim();
  if (!output) return [];
  return output.split(/\r?\n/).filter(Boolean);
}

const files = Array.from(new Set(patterns.flatMap(expand))).sort();
if (files.length === 0) {
  console.error('No files matched the provided globs.');
  process.exit(1);
}

const schemaFullPath = path.resolve(schemaPath);
const schema = JSON.parse(readFileSync(schemaFullPath, 'utf8'));
const useAjv2020 = typeof schema.$schema === 'string' && schema.$schema.includes('2020-12');
const AjvCtor = useAjv2020 ? Ajv2020 : AjvDraft;
const ajv = new AjvCtor({
  allErrors: true,
  strict,
  allowUnionTypes: true,
  coerceTypes: false,
  useDefaults: false,
});
addFormats(ajv);
const validate = ajv.compile(schema);

let failed = false;
for (const file of files) {
  const data = JSON.parse(readFileSync(file, 'utf8'));
  const ok = validate(data);
  if (!ok) {
    failed = true;
    console.error(`${file}: FAIL`);
    for (const err of validate.errors || []) {
      const location = err.instancePath || '/';
      console.error(`  - ${location}: ${err.message}`);
    }
  }
}

if (failed) {
  process.exit(1);
}
console.log(`Validated ${files.length} file(s) against ${schemaPath}`);
