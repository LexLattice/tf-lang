#!/usr/bin/env node
import { parseArgs } from 'node:util';
import readline from 'node:readline';

const {
  values: { prim, effect, grep, pretty },
} = parseArgs({
  options: {
    prim: { type: 'string' },
    effect: { type: 'string' },
    grep: { type: 'string' },
    pretty: { type: 'boolean' },
  },
});

const grepNeedle = typeof grep === 'string' ? grep.toLowerCase() : undefined;
const shouldPrettyPrint = Boolean(pretty);

const rl = readline.createInterface({
  input: process.stdin,
  crlfDelay: Infinity,
});

rl.on('line', (line) => {
  if (!line.trim()) {
    return;
  }

  let record;
  try {
    record = JSON.parse(line);
  } catch (err) {
    return;
  }

  if (record === null || typeof record !== 'object') {
    return;
  }

  if (prim && record?.prim_id !== prim) {
    return;
  }

  if (effect && record?.effect !== effect) {
    return;
  }

  if (grepNeedle) {
    const tagValue = record?.tag;
    let tagString = '';
    if (typeof tagValue === 'string') {
      tagString = tagValue;
    } else if (tagValue !== undefined) {
      try {
        const json = JSON.stringify(tagValue);
        tagString = typeof json === 'string' ? json : String(tagValue ?? '');
      } catch (err) {
        tagString = String(tagValue ?? '');
      }
    }

    if (!tagString.toLowerCase().includes(grepNeedle)) {
      return;
    }
  }

  const output = shouldPrettyPrint
    ? JSON.stringify(record, null, 2)
    : JSON.stringify(record);

  process.stdout.write(`${output}\n`);
});
