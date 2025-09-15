import { promises as fs } from 'fs';
import Ajv from 'ajv';

const readJson = async (path) => {
  try {
    const txt = await fs.readFile(path, 'utf8');
    return { ok: true, value: JSON.parse(txt) };
  } catch (err) {
    return { ok: false, error: err?.message ?? String(err) };
  }
};

const schema = JSON.parse(await fs.readFile('schema/tf-spec.schema.json', 'utf8'));
const ajv = new Ajv();
const validate = ajv.compile(schema);

const dir = 'examples/specs';
const files = (await fs.readdir(dir))
  .filter(f => f.endsWith('.json'))
  .map(f => `${dir}/${f}`)
  .sort((a, b) => a.localeCompare(b));

const lines = [];
let ok = true;

for (const file of files) {
  // Read and parse JSON per-file; never abort the whole run
  const parsed = await readJson(file);
  if (!parsed.ok) {
    ok = false;
    lines.push(`${file}: FAIL parse=1`);
    lines.push(` - [parse] / ${parsed.error}`);
    continue;
  }

  const data = parsed.value;
  const valid = validate(data);
  if (!valid) {
    ok = false;
    const errs = (validate.errors ?? []);
    // Tally by Ajv keyword (acts as error code)
    const tallies = new Map();
    for (const e of errs) {
      const k = e.keyword || 'unknown';
      tallies.set(k, (tallies.get(k) || 0) + 1);
    }
    const summary = Array.from(tallies.entries())
      .sort((a, b) => a[0].localeCompare(b[0]))
      .map(([k, v]) => `${k}=${v}`)
      .join(' ');
    lines.push(`${file}: FAIL ${summary}`);
    for (const e of errs) {
      const code = e.keyword || 'unknown';
      const path = e.instancePath && e.instancePath !== '' ? e.instancePath : '/';
      const msg = e.message || '';
      lines.push(` - [${code}] ${path} ${msg}`);
    }
  } else {
    lines.push(`${file}: OK`);
  }
}

await fs.mkdir('tf-spec', { recursive: true });
const out = lines.join('\n') + '\n';
await fs.writeFile('tf-spec/validation.txt', out);
console.log(out);
if (!ok) process.exit(1);
