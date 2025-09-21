import { createHash } from 'node:crypto';
import { createReadStream } from 'node:fs';
import readline from 'node:readline';

function canonicalize(value) {
  if (typeof value === 'bigint') {
    return { $bigint: value.toString(10) };
  }
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  if (value && typeof value === 'object') {
    const result = {};
    const keys = Object.keys(value).sort();
    for (const key of keys) {
      result[key] = canonicalize(value[key]);
    }
    return result;
  }
  return value;
}

export function sha256OfCanonicalJson(value) {
  const canonical = canonicalize(value);
  const json = JSON.stringify(canonical);
  const hash = createHash('sha256');
  hash.update(json);
  return `sha256:${hash.digest('hex')}`;
}

export async function sha256OfJsonl(filePath) {
  const hash = createHash('sha256');
  const stream = createReadStream(filePath, { encoding: 'utf8' });
  const rl = readline.createInterface({ input: stream, crlfDelay: Infinity });
  try {
    for await (const line of rl) {
      const trimmed = line.trim();
      hash.update(trimmed, 'utf8');
      hash.update('\n');
    }
  } finally {
    rl.close();
  }
  return `sha256:${hash.digest('hex')}`;
}
