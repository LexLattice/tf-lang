#!/usr/bin/env node

import { mkdir, readFile, writeFile } from 'node:fs/promises';
import process from 'node:process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';

const usage = 'Usage: node packages/tf-compose/bin/tf-manifest.mjs <flow.tf> [-o out.json]';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      out: { type: 'string', short: 'o' }
    },
    allowPositionals: true
  });

  if (positionals.length === 0) {
    throw new Error('Missing flow path');
  }
  if (positionals.length > 1) {
    throw new Error(`Unexpected argument: ${positionals[1]}`);
  }

  const flowPath = positionals[0];
  const outPath = values.out;

  const [{ parseDSL }, { checkIR }, { manifestFromVerdict }] = await Promise.all([
    import('../src/parser.mjs'),
    import('../../tf-l0-check/src/check.mjs'),
    import('../../tf-l0-check/src/manifest.mjs')
  ]);

  let flowSource;
  try {
    flowSource = await readFile(flowPath, 'utf8');
  } catch (err) {
    throw new Error(`Failed to read flow at ${flowPath}: ${err.message}`);
  }
  const ir = parseDSL(flowSource);

  const scriptDir = path.dirname(fileURLToPath(import.meta.url));
  const catalogPath = path.resolve(
    scriptDir,
    '..',
    '..',
    'tf-l0-spec/spec/catalog.json'
  );
  let catalog;
  try {
    catalog = JSON.parse(await readFile(catalogPath, 'utf8'));
  } catch (err) {
    throw new Error(`Failed to load catalog at ${catalogPath}: ${err.message}`);
  }

  const verdict = checkIR(ir, catalog);
  const manifest = manifestFromVerdict(verdict);
  const json = JSON.stringify(manifest, null, 2);

  if (outPath) {
    await mkdir(path.dirname(outPath), { recursive: true });
    await writeFile(outPath, `${json}\n`, 'utf8');
  } else {
    console.log(json);
  }

  if (verdict && verdict.ok === false) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  console.error(err.message || err);
  console.error(usage);
  process.exit(1);
});
