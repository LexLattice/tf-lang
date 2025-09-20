#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import Ajv from 'ajv/dist/2020.js';   // <-- use 2020 draft build

const ajv = new Ajv({ strict: true, allErrors: true });
const schema = JSON.parse(await readFile('schemas/ids.schema.json', 'utf8'));
const validate = ajv.compile(schema);

const data = JSON.parse(await readFile('packages/tf-l0-spec/spec/ids.json', 'utf8'));
const ok = validate(data);
if (!ok) {
  console.error("IDs schema validation failed:");
  for (const err of validate.errors || []) console.error("-", ajv.errorsText([err], { separator: "\n  " }));
  process.exit(1);
}
console.log("IDs file is valid.");
