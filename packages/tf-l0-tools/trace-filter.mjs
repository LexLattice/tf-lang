#!/usr/bin/env node
import { parseArgs } from 'node:util';
import { createInterface } from 'node:readline';

const {
  values: { prim, effect, grep, pretty, help },
  positionals,
} = parseArgs({
  options: {
    prim: { type: 'string' },
    effect: { type: 'string' },
    grep: { type: 'string' },
    pretty: { type: 'boolean', default: false },
    help: { type: 'boolean', default: false },
  },
  allowPositionals: true,
});

if (positionals.length > 0) {
  console.error('trace-filter: unexpected positional arguments:', positionals.join(' '));
  process.exit(1);
}

if (help) {
  console.log('Usage: trace-filter [--prim=id] [--effect=name] [--grep=substring] [--pretty]');
  console.log('Reads JSONL traces from stdin and emits the filtered subset to stdout.');
  process.exit(0);
}

const matcher = createMatcher({ prim, effect, grep });
const rl = createInterface({
  input: process.stdin,
  crlfDelay: Infinity,
});

let wroteAny = false;

rl.on('line', (line) => {
  const record = parseLine(line);
  if (!record) {
    return;
  }
  if (!matcher(record)) {
    return;
  }
  const json = pretty ? JSON.stringify(record, null, 2) : JSON.stringify(record);
  if (wroteAny) {
    process.stdout.write('\n');
  }
  process.stdout.write(json);
  wroteAny = true;
});

rl.on('close', () => {
  if (wroteAny) {
    process.stdout.write('\n');
  }
});

function parseLine(line) {
  const trimmed = line.trim();
  if (trimmed.length === 0) {
    return null;
  }
  try {
    return JSON.parse(trimmed);
  } catch (error) {
    return null;
  }
}

function createMatcher({ prim, effect, grep }) {
  const lowered = grep ? grep.toLowerCase() : null;
  return (record) => {
    if (prim && record.prim_id !== prim) {
      return false;
    }
    if (effect && record.effect !== effect) {
      return false;
    }
    if (lowered) {
      let tagValue = '';
      if (record.tag !== undefined) {
        try {
          tagValue = typeof record.tag === 'string' ? record.tag : JSON.stringify(record.tag) ?? '';
        } catch (error) {
          tagValue = '';
        }
      }
      if (!tagValue || !tagValue.toLowerCase().includes(lowered)) {
        return false;
      }
    }
    return true;
  };
}
