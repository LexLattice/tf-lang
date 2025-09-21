#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

function canonicalize(value) {
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  const out = {};
  for (const key of Object.keys(value).sort()) {
    const canonical = canonicalize(value[key]);
    if (canonical !== undefined) {
      out[key] = canonical;
    }
  }
  return out;
}

function canonicalString(value) {
  if (value === null) return 'null';
  const type = typeof value;
  if (type === 'number') {
    if (!Number.isFinite(value)) {
      throw new Error(`non-finite number in canonicalization: ${value}`);
    }
    return JSON.stringify(value);
  }
  if (type === 'bigint') {
    return JSON.stringify(Number(value));
  }
  if (type !== 'object') {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((entry) => canonicalString(entry)).join(',')}]`;
  }
  const keys = Object.keys(value).sort();
  return `{${keys.map((key) => `${JSON.stringify(key)}:${canonicalString(value[key])}`).join(',')}}`;
}

function sha256ForString(source) {
  return `sha256:${createHash('sha256').update(source).digest('hex')}`;
}

export function canonicalSha256ForJson(value) {
  const canonical = canonicalString(canonicalize(value));
  return sha256ForString(canonical);
}

export function hashJsonOrJsonl(raw) {
  if (typeof raw !== 'string') {
    throw new TypeError('hashJsonOrJsonl expects string input');
  }
  const trimmed = raw.trim();
  if (!trimmed) {
    return sha256ForString('');
  }
  try {
    const parsed = JSON.parse(raw);
    return canonicalSha256ForJson(parsed);
  } catch (err) {
    const lines = raw.split(/\r?\n/).filter((line) => line.trim().length > 0);
    const canonicalLines = lines.map((line, idx) => {
      try {
        const parsed = JSON.parse(line);
        return canonicalString(canonicalize(parsed));
      } catch (inner) {
        const label = `line ${idx + 1}`;
        const message = inner?.message ?? inner;
        throw new Error(`unable to parse JSONL ${label}: ${message}`);
      }
    });
    const joined = `${canonicalLines.join('\n')}\n`;
    return sha256ForString(joined);
  }
}

export function hashFile(path) {
  const raw = readFileSync(path, 'utf8');
  return hashJsonOrJsonl(raw);
}

const isCli = (() => {
  const entry = process.argv[1];
  if (!entry) return false;
  try {
    const entryUrl = new URL(entry, `file://${process.cwd()}/`);
    return fileURLToPath(import.meta.url) === fileURLToPath(entryUrl);
  } catch {
    return false;
  }
})();

if (isCli) {
  const args = process.argv.slice(2);
  if (args.length === 0) {
    console.error('usage: node scripts/hash-jsonl.mjs <file> [...file]');
    process.exit(1);
  }
  for (const target of args) {
    try {
      const digest = hashFile(target);
      process.stdout.write(`${digest}  ${target}\n`);
    } catch (err) {
      console.error(`error hashing ${target}:`, err?.message ?? err);
      process.exit(1);
    }
  }
}
