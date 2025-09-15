import { promises as fs } from 'node:fs';
import { join } from 'node:path';
import Ajv from 'ajv/dist/2020.js';

const schemaPath = 'schema/tf-spec.schema.json';
const examplesDir = 'examples/specs';
const ajv = new Ajv();

const schema = JSON.parse(await fs.readFile(schemaPath, 'utf8'));
const validate = ajv.compile(schema);

const files = (await fs.readdir(examplesDir)).filter(f => f.endsWith('.json'));
let output = '';
for (const file of files) {
  const data = JSON.parse(await fs.readFile(join(examplesDir, file), 'utf8'));
  const valid = validate(data);
  if (!valid) {
    console.error(validate.errors);
    throw new Error(`invalid: ${file}`);
  }
  const line = `${file} OK`;
  console.log(line);
  output += line + '\n';
}
await fs.mkdir('tf-spec', { recursive: true });
await fs.writeFile('tf-spec/validation.txt', output);
