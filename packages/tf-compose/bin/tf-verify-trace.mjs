#!/usr/bin/env node

import { readFile } from 'node:fs/promises';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { canonicalJson, verifyTrace } from '../../tf-l0-tools/verify-trace.mjs';

const usage = 'Usage: node packages/tf-compose/bin/tf-verify-trace.mjs --ir <file.ir.json> --trace <file.jsonl> [--manifest <manifest.json>] [--catalog <catalog.json>]';

function parseJsonl(content, source) {
  const records = [];
  const lines = content.split(/\r?\n/);
  for (let i = 0; i < lines.length; i += 1) {
    const raw = lines[i];
    const line = raw.trim();
    if (!line) continue;
    try {
      records.push(JSON.parse(line));
    } catch (err) {
      const message = err && err.message ? err.message : String(err);
      throw new Error(`Failed to parse JSON on line ${i + 1} of ${source}: ${message}`);
    }
  }
  return records;
}

async function loadJson(path) {
  const text = await readFile(path, 'utf8');
  try {
    return JSON.parse(text);
  } catch (err) {
    const message = err && err.message ? err.message : String(err);
    throw new Error(`Failed to parse JSON from ${path}: ${message}`);
  }
}

async function main(argv) {
  const { values } = parseArgs({
    args: argv.slice(2),
    options: {
      ir: { type: 'string' },
      trace: { type: 'string' },
      manifest: { type: 'string' },
      catalog: { type: 'string' },
    },
  });

  if (!values.ir || !values.trace) {
    throw new Error('Missing required arguments --ir and --trace');
  }

  const ir = await loadJson(values.ir);
  const traceText = await readFile(values.trace, 'utf8');
  const trace = parseJsonl(traceText, values.trace);

  const manifest = values.manifest ? await loadJson(values.manifest) : null;
  const catalog = values.catalog ? await loadJson(values.catalog) : null;

  const result = verifyTrace(ir, trace, { manifest, catalog });
  const output = canonicalJson(result);
  process.stdout.write(output + '\n');

  if (!result.ok) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  const message = err && err.message ? err.message : String(err);
  console.error(message);
  console.error(usage);
  process.exitCode = 2;
});
