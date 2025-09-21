import { createInterface } from 'node:readline';
import { stdin, stdout } from 'node:process';
import { readFile } from 'node:fs/promises';
import Ajv from 'ajv/dist/2020.js';

const schemaUrl = new URL('../schemas/trace.v0.4.schema.json', import.meta.url);
const schema = JSON.parse(await readFile(schemaUrl, 'utf8'));

const ajv = new Ajv({ strict: true, allErrors: true });
const validate = ajv.compile(schema);

const rl = createInterface({
  input: stdin,
  crlfDelay: Infinity,
});

let total = 0;
let invalid = 0;
let lineNumber = 0;
const examples = [];

for await (const line of rl) {
  lineNumber += 1;
  if (!line.trim()) continue;
  total += 1;

  let record;
  try {
    record = JSON.parse(line);
  } catch (err) {
    invalid += 1;
    if (examples.length < 3) {
      examples.push({ line: lineNumber, error: `invalid JSON: ${err.message}` });
    }
    continue;
  }

  if (!validate(record)) {
    invalid += 1;
    const firstError = validate.errors?.[0];
    let message = 'invalid record';
    if (firstError) {
      if (firstError.keyword === 'required' && firstError.params?.missingProperty) {
        message = `${firstError.params.missingProperty} is required`;
      } else if (typeof firstError.message === 'string') {
        message = firstError.message;
      } else {
        message = ajv.errorsText([firstError]);
      }
    }
    if (examples.length < 3) {
      examples.push({ line: lineNumber, error: message });
    }
  }
}

const ok = invalid === 0;
const summary = ok
  ? { ok: true, total, invalid: 0 }
  : { ok: false, total, invalid, examples };

stdout.write(`${JSON.stringify(summary)}\n`);
process.exitCode = ok ? 0 : 1;
