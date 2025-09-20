#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';

const [,, manifestPath] = process.argv;

if (!manifestPath) {
  console.error('Usage: node scripts/validate-manifest.mjs <manifest.json>');
  process.exit(1);
}

const __dirname = dirname(fileURLToPath(import.meta.url));
const schemaPath = resolve(__dirname, '../schemas/manifest.v0.4.schema.json');

async function main() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  const schema = JSON.parse(await readFile(schemaPath, 'utf8'));
  const validate = ajv.compile(schema);
  const manifest = JSON.parse(await readFile(manifestPath, 'utf8'));

  const valid = validate(manifest);
  if (valid) {
    console.log('Manifest OK');
    return;
  }

  console.error('Manifest validation failed.');
  if (validate.errors) {
    const details = ajv.errorsText(validate.errors, { separator: '\n' });
    console.error(details);
  }
  process.exit(1);
}

main().catch((err) => {
  console.error('Manifest validation failed.');
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
