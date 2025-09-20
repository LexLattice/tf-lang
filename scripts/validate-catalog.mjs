#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import Ajv from 'ajv';
const ajv = new Ajv({ strict: true, allErrors: true });
const catalogSchema = JSON.parse(await readFile('schemas/catalog.schema.json','utf8'));
const primitiveSchema = JSON.parse(await readFile('schemas/primitive.schema.json','utf8'));
ajv.addSchema(primitiveSchema, primitiveSchema.$id);
const validate = ajv.compile(catalogSchema);
const data = JSON.parse(await readFile('packages/tf-l0-spec/spec/catalog.json','utf8'));
const ok = validate(data);
if (!ok) {
  console.error("Catalog schema validation failed:");
  for (const err of validate.errors || []) console.error("-", ajv.errorsText([err], { separator: "\n  " }));
  process.exit(1);
}
console.log("Catalog is valid.");
