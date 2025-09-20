#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import Ajv from 'ajv/dist/2020.js';

async function main() {
  const [manifestPath] = process.argv.slice(2);

  if (!manifestPath) {
    console.error('Usage: node scripts/validate-manifest.mjs <manifest.json>');
    process.exit(1);
    return;
  }

  const schemaPath = path.resolve(
    path.dirname(fileURLToPath(import.meta.url)),
    '..',
    'schemas',
    'manifest.v0.4.schema.json'
  );

  const [schemaJSON, manifestJSON] = await Promise.all([
    readFile(schemaPath, 'utf8'),
    readFile(manifestPath, 'utf8')
  ]);

  const schema = JSON.parse(schemaJSON);
  const manifest = JSON.parse(manifestJSON);

  const ajv = new Ajv({ strict: true, allErrors: true });
  const validate = ajv.compile(schema);

  if (validate(manifest)) {
    console.log('Manifest OK');
    return;
  }

  console.error('Manifest validation failed.');
  for (const error of validate.errors ?? []) {
    console.error(`- ${error.instancePath || '/'}: ${error.message}`);
  }
  process.exit(1);
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : error);
  process.exit(1);
});
