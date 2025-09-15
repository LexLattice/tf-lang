import { promises as fs } from 'fs';
import Ajv from 'ajv';

const schema = JSON.parse(await fs.readFile('schema/tf-spec.schema.json', 'utf8'));
const ajv = new Ajv();
const validate = ajv.compile(schema);
const files = (await fs.readdir('examples/specs')).filter(f => f.endsWith('.json'));
let lines = [];
for (const file of files) {
  const data = JSON.parse(await fs.readFile(`examples/specs/${file}`, 'utf8'));
  if (!validate(data)) {
    console.error('Invalid', file, validate.errors);
    process.exit(1);
  }
  lines.push(`${file}: OK`);
}
await fs.mkdir('tf-spec', { recursive: true });
await fs.writeFile('tf-spec/validation.txt', lines.join('\n') + '\n');
console.log(lines.join('\n'));

