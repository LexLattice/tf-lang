import { createRequire } from 'node:module';
import { createInterface } from 'node:readline';
import Ajv2020 from 'ajv/dist/2020.js';

const require = createRequire(import.meta.url);
const schema = require('../schemas/trace.v0.4.schema.json');

const ajv = new Ajv2020({ allErrors: true, strict: false });
const validate = ajv.compile(schema);

const rl = createInterface({
  input: process.stdin,
  crlfDelay: Number.POSITIVE_INFINITY,
});

process.stdin.setEncoding('utf8');

let total = 0;
let invalid = 0;
const examples = [];
let lineNumber = 0;

function addExample(line, error) {
  if (examples.length < 3) {
    examples.push({ line, error });
  }
}

function describeError(error) {
  if (!error) return 'invalid record';
  if (error.keyword === 'required' && error.params && typeof error.params.missingProperty === 'string') {
    return `${error.params.missingProperty} is required`;
  }
  if (typeof error.message === 'string' && error.message.length > 0) {
    return error.message;
  }
  return 'invalid record';
}

(async () => {
  for await (const raw of rl) {
    lineNumber += 1;
    if (!raw.trim()) {
      continue;
    }
    total += 1;
    let parsed;
    try {
      parsed = JSON.parse(raw);
    } catch (err) {
      invalid += 1;
      addExample(lineNumber, 'invalid JSON');
      continue;
    }
    if (!validate(parsed)) {
      invalid += 1;
      addExample(lineNumber, describeError(validate.errors && validate.errors[0]));
    }
  }

  const summary = { ok: invalid === 0, total, invalid };
  if (invalid > 0) {
    summary.examples = examples;
  }

  if (invalid > 0) {
    process.exitCode = 1;
  }

  process.stdout.write(JSON.stringify(summary) + '\n');
})();
