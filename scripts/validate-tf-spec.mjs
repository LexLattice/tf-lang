import { readdirSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import Ajv from 'ajv';

const ajv = new Ajv({ allErrors: true });
const schema = JSON.parse(readFileSync('schema/tf-spec.schema.json', 'utf8'));
const validate = ajv.compile(schema);
const files = readdirSync('examples/specs').filter(f => f.endsWith('.json'));
let out = '';
for (const f of files) {
  const data = JSON.parse(readFileSync(`examples/specs/${f}`, 'utf8'));
  if (!validate(data)) {
    console.error(f, validate.errors);
    process.exit(1);
  }
  out += `${f}: OK\n`;
}
mkdirSync('tf-spec', { recursive: true });
writeFileSync('tf-spec/validation.txt', out);
console.log(out);
