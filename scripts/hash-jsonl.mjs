#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

export function canonicalize(value) {
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  const result = {};
  for (const key of Object.keys(value).sort()) {
    const normalized = canonicalize(value[key]);
    if (normalized !== undefined) {
      result[key] = normalized;
    }
  }
  return result;
}

export function canonicalStringify(value) {
  return JSON.stringify(canonicalize(value));
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
