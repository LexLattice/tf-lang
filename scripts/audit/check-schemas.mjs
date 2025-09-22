#!/usr/bin/env node
// scripts/audit/check-schemas.mjs
import { readFile, readdir } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import Ajv2020 from 'ajv/dist/2020.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '../..');
const SCHEMA_DIR = path.join(ROOT, 'schemas');

async function loadSchemaFiles() {
  const entries = await readdir(SCHEMA_DIR, { withFileTypes: true });
  const files = entries
    .filter((entry) => entry.isFile() && entry.name.endsWith('.json'))
    .map((entry) => entry.name)
    .sort();

  const loaded = [];
  const results = [];
  for (const name of files) {
    const relPath = path.posix.join('schemas', name);
    const absPath = path.join(SCHEMA_DIR, name);
    try {
      const raw = await readFile(absPath, 'utf8');
      const schema = JSON.parse(raw);
      loaded.push({ name, schema, relPath });
    } catch (err) {
      const message = err?.message ? String(err.message) : String(err);
      results.push({ file: relPath, ok: false, errors: [`parse_error: ${message}`] });
    }
  }

  return { loaded, results };
}

function extractErrors(err) {
  if (!err) return [];
  const messages = [];
  if (Array.isArray(err.errors)) {
    for (const detail of err.errors) {
      if (detail && typeof detail === 'object') {
        const instancePath = detail.instancePath || detail.dataPath || '';
        const keyword = detail.keyword ? ` (${detail.keyword})` : '';
        const base = detail.message ? String(detail.message) : JSON.stringify(detail);
        messages.push(`${instancePath || '<root>'}${keyword}: ${base}`);
      } else {
        messages.push(String(detail));
      }
    }
  }
  if (err.message) {
    messages.push(String(err.message));
  }
  return messages.length > 0 ? messages : [String(err)];
}

export async function run() {
  const { loaded, results } = await loadSchemaFiles();

  for (const { name, schema, relPath } of loaded) {
    const ajv = new Ajv2020({ strict: true, allErrors: true });
    let failed = false;
    for (const { schema: otherSchema, name: otherName } of loaded) {
      const key = otherSchema && typeof otherSchema === 'object' && otherSchema.$id ? otherSchema.$id : otherName;
      try {
        ajv.addSchema(otherSchema, key);
      } catch (err) {
        // addSchema may throw if duplicate IDs; capture as compile error below
        results.push({
          file: relPath,
          ok: false,
          errors: [`add_schema_failed (${key}): ${err?.message || err}`]
        });
        failed = true;
        break;
      }
    }
    if (failed || results.some((entry) => entry.file === relPath && entry.ok === false)) {
      continue;
    }
    try {
      const identifier = schema && typeof schema === 'object' && schema.$id ? schema.$id : name;
      const validate = ajv.getSchema(identifier) || ajv.compile(schema);
      if (typeof validate !== 'function') {
        results.push({ file: relPath, ok: false, errors: ['compile_failed: validator not created'] });
      } else {
        results.push({ file: relPath, ok: true });
      }
    } catch (err) {
      const errors = extractErrors(err);
      results.push({ file: relPath, ok: false, errors });
    }
  }

  // Deduplicate entries when addSchema failure already pushed an error
  const byFile = new Map();
  for (const entry of results) {
    const current = byFile.get(entry.file);
    if (!current) {
      byFile.set(entry.file, entry);
      continue;
    }
    if (!current.ok) {
      // keep first failure
      continue;
    }
    byFile.set(entry.file, entry);
  }

  const entries = Array.from(byFile.values()).sort((a, b) => a.file.localeCompare(b.file));
  const ok = entries.every((entry) => entry.ok);
  return { ok, entries };
}

async function main() {
  const result = await run();
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
}

const isCli = process.argv[1]
  ? pathToFileURL(process.argv[1]).href === import.meta.url
  : false;

if (isCli) {
  main().catch((err) => {
    process.stderr.write(`audit:check-schemas failed: ${err?.stack || err}\n`);
    process.exitCode = 1;
  });
}
