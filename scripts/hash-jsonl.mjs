#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { extname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

function canonicalize(value) {
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  const out = {};
  for (const key of Object.keys(value).sort()) {
    const canon = canonicalize(value[key]);
    if (canon !== undefined) {
      out[key] = canon;
    }
  }
  return out;
}

function canonicalJsonString(value) {
  return JSON.stringify(canonicalize(value));
}

async function canonicalPayloadFor(path, mode) {
  const raw = await readFile(path, 'utf8');
  const detected = mode ?? inferMode(path);
  if (detected === 'jsonl') {
    const lines = raw
      .split(/\r?\n/)
      .map((line) => line.trim())
      .filter((line) => line.length > 0);
    const normalized = lines.map((line) => canonicalJsonString(JSON.parse(line)));
    return normalized.join('\n');
  }
  const json = JSON.parse(raw);
  return canonicalJsonString(json);
}

function inferMode(path) {
  const ext = extname(path).toLowerCase();
  if (ext === '.jsonl' || ext === '.ndjson' || ext === '.jsonl.gz') {
    return 'jsonl';
  }
  return 'json';
}

export async function hashJsonFile(path, options = {}) {
  const payload = await canonicalPayloadFor(path, options.mode);
  const digest = createHash('sha256').update(payload, 'utf8').digest('hex');
  return {
    digest: `sha256:${digest}`,
    payload,
  };
}

async function main(argv) {
  const paths = argv.slice(2);
  if (paths.length === 0) {
    console.error('usage: node scripts/hash-jsonl.mjs <file> [file...]');
    process.exitCode = 1;
    return;
  }
  for (const path of paths) {
    const { digest } = await hashJsonFile(path);
    process.stdout.write(`${digest}  ${path}\n`);
  }
}

const invokedDirectly = process.argv[1]
  ? import.meta.url === pathToFileURL(resolve(process.argv[1])).href
  : false;

if (invokedDirectly) {
  await main(process.argv);
}
