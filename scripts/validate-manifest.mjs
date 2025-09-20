#!/usr/bin/env node

import { readFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';

const usage = 'Usage: node scripts/validate-manifest.mjs <manifest.json>';

async function loadSchema() {
  const scriptDir = path.dirname(fileURLToPath(import.meta.url));
  const schemaPath = path.resolve(scriptDir, '..', 'schemas', 'manifest.v0.4.schema.json');
  try {
    const schemaSource = await readFile(schemaPath, 'utf8');
    return JSON.parse(schemaSource);
  } catch (err) {
    throw new Error(`Failed to load schema from ${schemaPath}: ${err.message}`);
  }
}

async function loadManifest(manifestPath) {
  try {
    const manifestSource = await readFile(manifestPath, 'utf8');
    return JSON.parse(manifestSource);
  } catch (err) {
    throw new Error(`Failed to read manifest at ${manifestPath}: ${err.message}`);
  }
}

function formatErrors(errors = []) {
  return errors
    .map((error) => {
      const instancePath = error.instancePath || '(root)';
      return `${instancePath} ${error.message}`;
    })
    .join('\n');
}

async function main(argv) {
  const manifestPath = argv[2];
  if (!manifestPath) {
    console.error(usage);
    process.exit(1);
    return;
  }

  const schema = await loadSchema();
  const ajv = new Ajv2020({ allErrors: true });
  const validate = ajv.compile(schema);
  const manifest = await loadManifest(manifestPath);

  const valid = validate(manifest);
  if (valid) {
    console.log('Manifest OK');
    return;
  }

  console.error('Manifest validation failed:');
  const details = formatErrors(validate.errors);
  if (details) {
    console.error(details);
  }
  process.exit(1);
}

main(process.argv).catch((err) => {
  console.error(err.message || err);
  process.exit(1);
});
