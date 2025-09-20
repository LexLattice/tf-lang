#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import Ajv from 'ajv/dist/2020.js';

async function main() {
  const [manifestPath] = process.argv.slice(2);
  if (!manifestPath) {
    console.error('Usage: node scripts/validate-manifest.mjs <manifest.json>');
    process.exit(1);
  }

  const ajv = new Ajv({ strict: true, allErrors: true });

  const schemaUrl = new URL('../schemas/manifest.v0.4.schema.json', import.meta.url);
  const schemaPath = fileURLToPath(schemaUrl);
  const schema = JSON.parse(await readFile(schemaPath, 'utf8'));
  const validate = ajv.compile(schema);

  let manifest;
  try {
    const raw = await readFile(path.resolve(manifestPath), 'utf8');
    manifest = JSON.parse(raw);
  } catch (err) {
    console.error(`Failed to read manifest from ${manifestPath}:`, err.message);
    process.exit(1);
  }

  const ok = validate(manifest);
  if (!ok) {
    console.error('Manifest validation failed:');
    for (const err of validate.errors || []) {
      console.error('-', ajv.errorsText([err], { separator: '\n  ' }));
    }
    process.exit(1);
  }

  console.log('Manifest OK');
}

await main();
