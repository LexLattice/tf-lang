import { createInterface } from 'node:readline';
import { parseArgs } from 'node:util';

const {
  values: { prim, effect, grep, pretty }
} = parseArgs({
  options: {
    prim: { type: 'string' },
    effect: { type: 'string' },
    grep: { type: 'string' },
    pretty: { type: 'boolean' }
  },
  allowPositionals: false
});

const grepNeedle = typeof grep === 'string' ? grep.toLowerCase() : null;

const rl = createInterface({
  input: process.stdin,
  crlfDelay: Infinity
});

rl.on('line', line => {
  const trimmed = line.trim();
  if (!trimmed) {
    return;
  }

  let entry;
  try {
    entry = JSON.parse(trimmed);
  } catch (error) {
    return;
  }

  if (prim && entry.prim_id !== prim) {
    return;
  }

  if (effect) {
    const effectValue = entry.effect;
    const effectFamily =
      typeof effectValue === 'string'
        ? effectValue
        : effectValue && typeof effectValue === 'object'
        ? effectValue.family
        : undefined;

    if (effectFamily !== effect) {
      return;
    }
  }

  if (grepNeedle) {
    const tagValue = entry.tag;
    const tagString =
      typeof tagValue === 'string'
        ? tagValue
        : tagValue == null
        ? ''
        : JSON.stringify(tagValue);

    if (!tagString.toLowerCase().includes(grepNeedle)) {
      return;
    }
  }

  const output = pretty ? JSON.stringify(entry, null, 2) : JSON.stringify(entry);
  process.stdout.write(output + '\n');
});

rl.on('close', () => {
  // no-op, allow process to exit naturally
});
