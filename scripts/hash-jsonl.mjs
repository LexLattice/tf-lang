#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const BIGINT_SENTINEL_KEY = '$bigint';

function isPlainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function isSetLikeArray(original) {
  if (!Array.isArray(original) || original.length < 2) return false;
  return original.every((entry) => {
    if (entry === null) return false;
    if (typeof entry === 'bigint') return true;
    if (Array.isArray(entry)) return false;
    if (isPlainObject(entry)) {
      if ('ts' in entry || 'timestamp' in entry) return false;
      return true;
    }
    switch (typeof entry) {
      case 'string':
      case 'number':
      case 'boolean':
        return true;
      default:
        return false;
    }
  });
}

export function canonReplacer(_key, value) {
  if (typeof value === 'bigint') {
    return { [BIGINT_SENTINEL_KEY]: value.toString(10) };
  }
  return value;
}

function canonicalizeInternal(value) {
  if (value === null) return null;
  if (typeof value === 'bigint') return value;
  if (Array.isArray(value)) {
    const normalized = value.map((entry) => canonicalizeInternal(entry));
    if (isSetLikeArray(normalized)) {
      return [...normalized].sort((a, b) => {
        const left = JSON.stringify(a, canonReplacer);
        const right = JSON.stringify(b, canonReplacer);
        if (left === right) return 0;
        return left < right ? -1 : 1;
      });
    }
    return normalized;
  }
  if (!isPlainObject(value)) {
    return value;
  }
  const entries = Object.entries(value)
    .filter(([, v]) => v !== undefined)
    .map(([key, val]) => [key, canonicalizeInternal(val)]);
  entries.sort(([a], [b]) => {
    if (a === b) return 0;
    return a < b ? -1 : 1;
  });
  const result = {};
  for (const [key, val] of entries) {
    result[key] = val;
  }
  return result;
}

export function canonicalize(value) {
  return canonicalizeInternal(value);
}

export function canonicalStringify(value) {
  return JSON.stringify(canonicalizeInternal(value), canonReplacer);
}

export async function canonicalContentFromFile(path) {
  const raw = await readFile(path, 'utf8');
  const trimmed = raw.trim();
  if (!trimmed) return '';
  try {
    const parsed = JSON.parse(trimmed);
    return canonicalStringify(parsed);
  } catch (err) {
    // Treat as JSONL
  }
  const lines = raw.split(/\r?\n/);
  const canonicalLines = [];
  for (const rawLine of lines) {
    const line = rawLine.trim();
    if (!line) continue;
    try {
      const parsed = JSON.parse(line);
      canonicalLines.push(canonicalStringify(parsed));
    } catch (err) {
      throw new Error(`Unable to parse JSON line from ${path}`);
    }
  }
  return canonicalLines.join('\n');
}

export function hashCanonical(content) {
  return 'sha256:' + createHash('sha256').update(content).digest('hex');
}

export async function hashJsonLike(path) {
  const canonical = await canonicalContentFromFile(path);
  return hashCanonical(canonical);
}

async function main(args) {
  if (args.length === 0) {
    console.error('usage: node scripts/hash-jsonl.mjs <file> [...]');
    process.exitCode = 1;
    return;
  }
  const result = {};
  for (const path of args) {
    result[path] = await hashJsonLike(path);
  }
  process.stdout.write(JSON.stringify(result, null, 2) + '\n');
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2);
  main(args).catch((err) => {
    console.error(err?.stack || err?.message || String(err));
    process.exitCode = 1;
  });
}
