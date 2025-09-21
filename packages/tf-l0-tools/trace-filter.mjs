#!/usr/bin/env node
import { parseArgs } from 'node:util';
import { createInterface } from 'node:readline';

const {
  values: { prim, effect, grep, pretty, help, quiet },
  positionals,
} = parseArgs({
  options: {
    prim: { type: 'string' },
    effect: { type: 'string' },
    grep: { type: 'string' },
    pretty: { type: 'boolean', default: false },
    help: { type: 'boolean', default: false },
    quiet: { type: 'boolean', default: false },
  },
  allowPositionals: true,
});

if (positionals.length > 0) {
  console.error('trace-filter: unexpected positional arguments:', positionals.join(' '));
  process.exit(1);
}

if (help) {
  console.log(
    'Usage: trace-filter [--prim=id] [--effect=name] [--grep=substring] [--pretty] [--quiet]'
  );
  console.log('Reads JSONL traces from stdin and emits the filtered subset to stdout.');
  process.exit(0);
}

const matcher = createMatcher({ prim, effect, grep });
const rl = createInterface({
  input: process.stdin,
  crlfDelay: Infinity,
});

rl.on('line', (line) => {
  const { record, invalid } = parseLine(line);
  if (invalid && !quiet) {
    process.stderr.write('warn: skipping invalid JSON line\n');
  }
  if (!record) {
    return;
  }
  if (!matcher(record)) {
    return;
  }
  const json = pretty ? JSON.stringify(record, null, 2) : JSON.stringify(record);
  process.stdout.write(json);
  process.stdout.write('\n');
});

function parseLine(line) {
  const trimmed = line.trim();
  if (trimmed.length === 0) {
    return { record: null, invalid: false };
  }
  try {
    return { record: JSON.parse(trimmed), invalid: false };
  } catch (error) {
    return { record: null, invalid: true };
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
      const haystacks = [];
      const collect = (value) => {
        if (value === undefined || value === null) return;
        if (typeof value === 'string') {
          haystacks.push(value);
          return;
        }
        try {
          const serialized = JSON.stringify(value);
          if (serialized) haystacks.push(serialized);
        } catch (error) {
          // ignore serialization errors and fall back to other sources
        }
      };

      collect(record.tag);
      collect(record.args);
      collect(record.payload);

      if (haystacks.length === 0) {
        return false;
      }

      const combined = haystacks.join(' ').toLowerCase();
      if (!combined.includes(lowered)) {
        return false;
      }
    }
    return true;
  };
}
