#!/usr/bin/env node
import { parseArgs } from 'node:util';
import readline from 'node:readline';

const {
  values: { prim, effect, grep, pretty }
} = parseArgs({
  options: {
    prim: { type: 'string' },
    effect: { type: 'string' },
    grep: { type: 'string' },
    pretty: { type: 'boolean', default: false }
  },
  allowPositionals: false
});

const grepLower = typeof grep === 'string' ? grep.toLowerCase() : null;

const rl = readline.createInterface({
  input: process.stdin,
  crlfDelay: Infinity
});

const writeRecord = (record) => {
  const json = pretty ? JSON.stringify(record, null, 2) : JSON.stringify(record);
  process.stdout.write(json);
  process.stdout.write('\n');
};

rl.on('line', (line) => {
  if (!line.trim()) {
    return;
  }

  let record;
  try {
    record = JSON.parse(line);
  } catch {
    return;
  }

  if (prim && record.prim_id !== prim) {
    return;
  }

  if (effect && record.effect !== effect) {
    return;
  }

  if (grepLower) {
    const tagValue = record.tag ?? '';
    let tagString = typeof tagValue === 'string' ? tagValue : JSON.stringify(tagValue);
    if (typeof tagString !== 'string') {
      tagString = '';
    }
    if (!tagString.toLowerCase().includes(grepLower)) {
      return;
    }
  }

  writeRecord(record);
});

rl.on('close', () => {
  // no-op, rely on process exit.
});
