import { promises as fs } from 'fs';
import Ajv from 'ajv';

const schema = JSON.parse(await fs.readFile('schema/tf-spec.schema.json', 'utf8'));
const ajv = new Ajv();
const validate = ajv.compile(schema);
const files = (await fs.readdir('examples/specs'))
  .filter(f => f.endsWith('.json'))
  .sort();
const lines = [];
let ok = true;
for (const file of files) {
  const data = JSON.parse(await fs.readFile(`examples/specs/${file}`, 'utf8'));
  if (!validate(data)) {
    ok = false;
    const errs = (validate.errors ?? [])
      .map(e => `${e.instancePath || '/'} ${e.message}`)
      .join('; ');
    lines.push(`${file}: ${errs}`);
  } else {
    lines.push(`${file}: OK`);
  }
}
await fs.mkdir('tf-spec', { recursive: true });
await fs.writeFile('tf-spec/validation.txt', lines.join('\n') + '\n');
console.log(lines.join('\n'));
if (!ok) process.exit(1);
