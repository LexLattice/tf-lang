import fs from 'fs';
import path from 'path';
import Ajv from 'ajv/dist/2020.js';

const schemaPath = path.resolve(path.dirname(new URL(import.meta.url).pathname), '../schema/tf-spec.schema.json');
const examplesDir = path.resolve(path.dirname(new URL(import.meta.url).pathname), '../examples/specs');
const outDir = path.resolve(path.dirname(new URL(import.meta.url).pathname), '../tf-spec');

const schema = JSON.parse(fs.readFileSync(schemaPath, 'utf8'));
const ajv = new Ajv();
const validate = ajv.compile(schema);

fs.mkdirSync(outDir, { recursive: true });
const lines = [];
for (const file of fs.readdirSync(examplesDir)) {
  if (!file.endsWith('.json')) continue;
  const data = JSON.parse(fs.readFileSync(path.join(examplesDir, file), 'utf8'));
  if (!validate(data)) {
    console.error(file, validate.errors);
    process.exit(1);
  }
  lines.push(`${file}: OK`);
}
fs.writeFileSync(path.join(outDir, 'validation.txt'), lines.join('\n'));
console.log(lines.join('\n'));
