#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import Ajv from 'ajv/dist/2020.js'; // use the 2020 draft build

const ajv = new Ajv({ strict: true, allErrors: true });

// Load root schema + all $ref’ed schemas
const catalogSchema = JSON.parse(await readFile('schemas/catalog.schema.json', 'utf8'));
const primitiveSchema = JSON.parse(await readFile('schemas/primitive.schema.json', 'utf8'));
const footprintSchema = JSON.parse(await readFile('schemas/footprint-pattern.schema.json', 'utf8'));
const errorTaxSchema = JSON.parse(await readFile('schemas/error-taxonomy.schema.json', 'utf8'));

// Register referenced schemas FIRST
ajv.addSchema(primitiveSchema, primitiveSchema.$id);
ajv.addSchema(footprintSchema, footprintSchema.$id);
ajv.addSchema(errorTaxSchema, errorTaxSchema.$id);

// Compile and validate
const validate = ajv.compile(catalogSchema);
const data = JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json', 'utf8'));
const ok = validate(data);

if (!ok) {
  console.error('Catalog schema validation failed:');
  for (const err of validate.errors || []) {
    console.error('-', ajv.errorsText([err], { separator: '\n  ' }));
  }
  process.exit(1);
}
console.log('Catalog is valid.');
