#!/usr/bin/env node
import { promises as fs } from 'fs';
import Ajv from 'ajv';

const schema = JSON.parse(await fs.readFile('schema/tf-spec.schema.json', 'utf8'));
const ajv = new Ajv({ allErrors: true });
const validate = ajv.compile(schema);
const files = (await fs.readdir('examples/specs')).filter(f => f.endsWith('.json')).sort();
let lines = [];
let errors = [];
for (const file of files) {
  const data = JSON.parse(await fs.readFile(`examples/specs/${file}`, 'utf8'));
  if (!validate(data)) {
    lines.push(`${file}: ERROR`);
    errors.push(`${file}\n${ajv.errorsText(validate.errors, { separator: '\n' })}`);
    continue;
  }
  lines.push(`${file}: OK`);
}
await fs.mkdir('tf-spec', { recursive: true });
await fs.writeFile('tf-spec/validation.txt', lines.join('\n') + '\n');
console.log(lines.join('\n'));
if (errors.length) {
  console.error("\nErrors:\n" + errors.join("\n\n"));
  process.exit(1);
}
process.exit(0);
