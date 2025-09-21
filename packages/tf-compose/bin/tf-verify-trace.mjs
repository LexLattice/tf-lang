#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { parseArgs } from 'node:util';

import { verifyTrace, canonicalJson } from '../../tf-l0-tools/verify-trace.mjs';

async function loadJson(path) {
  try {
    const data = await readFile(path, 'utf8');
    return JSON.parse(data);
  } catch (err) {
    throw new Error(`failed to read ${path}: ${err.message}`);
  }
}

async function loadText(path) {
  try {
    return await readFile(path, 'utf8');
  } catch (err) {
    throw new Error(`failed to read ${path}: ${err.message}`);
  }
}

async function main() {
  const { values } = parseArgs({
    options: {
      ir: { type: 'string' },
      trace: { type: 'string' },
      manifest: { type: 'string' },
      catalog: { type: 'string' },
    },
  });

  if (!values.ir || !values.trace) {
    console.error('Usage: tf-verify-trace --ir <file.ir.json> --trace <file.jsonl> [--manifest <manifest.json>] [--catalog <catalog.json>]');
    process.exit(2);
  }

  try {
    const ir = await loadJson(values.ir);
    const trace = await loadText(values.trace);
    const manifest = values.manifest ? await loadJson(values.manifest) : null;
    const catalog = values.catalog ? await loadJson(values.catalog) : null;

    const result = verifyTrace({ ir, trace, manifest, catalog });
    process.stdout.write(canonicalJson(result) + '\n');
    process.exit(result.ok ? 0 : 1);
  } catch (err) {
    console.error(err.message || String(err));
    process.exit(2);
  }
}

await main();
