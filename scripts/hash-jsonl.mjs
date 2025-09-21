#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { basename, resolve } from 'node:path';

export function canonicalize(value) {
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  const out = {};
  for (const key of Object.keys(value).sort()) {
    const next = canonicalize(value[key]);
    if (next !== undefined) {
      out[key] = next;
    }
  }
  return out;
}

export function canonicalStringify(value) {
  return JSON.stringify(canonicalize(value));
}

export function hashCanonicalString(text) {
  const hash = createHash('sha256');
  hash.update(text);
  return `sha256:${hash.digest('hex')}`;
}

export function hashJsonText(text, { jsonl = false } = {}) {
  if (!jsonl) {
    const data = text.trim();
    if (!data) {
      return hashCanonicalString('');
    }
    const value = JSON.parse(data);
    return hashCanonicalString(canonicalStringify(value));
  }

  const lines = text
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
  const canonical = lines.map((line) => {
    const value = JSON.parse(line);
    return canonicalStringify(value);
  });
  return hashCanonicalString(canonical.join('\n'));
}

export function hashJsonFile(path, opts = {}) {
  const raw = readFileSync(path, 'utf8');
  const jsonl = Object.prototype.hasOwnProperty.call(opts, 'jsonl') ? opts.jsonl : path.endsWith('.jsonl');
  return hashJsonText(raw, { jsonl });
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2);
  if (args.length === 0) {
    console.error(`usage: node ${basename(fileURLToPath(import.meta.url))} <file> [--jsonl]`);
    process.exit(1);
  }
  const flags = new Set(args.slice(1));
  const jsonl = flags.has('--jsonl');
  const file = args[0];
  try {
    const digest = hashJsonFile(file, { jsonl });
    console.log(digest);
  } catch (err) {
    console.error(err?.message ?? err);
    process.exit(1);
  }
}
