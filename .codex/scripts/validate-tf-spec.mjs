import { promises as fs } from 'fs';
import Ajv from 'ajv';

const schema = JSON.parse(await fs.readFile('schema/tf-spec.schema.json', 'utf8'));
const ajv = new Ajv({ allErrors: true });
const validate = ajv.compile(schema);
const files = (await fs.readdir('examples/specs')).filter(f => f.endsWith('.json'));
const lines = [];
let failures = 0;
for (const file of files) {
  const data = JSON.parse(await fs.readFile(`examples/specs/${file}`, 'utf8'));
  if (!validate(data)) {
    failures++;
    const msg = ajv.errorsText(validate.errors, { separator: '; ' });
    lines.push(`${file}: ${msg}`);
    continue;
  }
  lines.push(`${file}: OK`);
}
await fs.mkdir('tf-spec', { recursive: true });
await fs.writeFile('tf-spec/validation.txt', lines.join('\n') + '\n');
console.log(lines.join('\n'));
console.log(`${files.length - failures} OK, ${failures} failed`);
if (failures > 0) process.exit(1);
