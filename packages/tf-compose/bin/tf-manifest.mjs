#!/usr/bin/env node

import { readFile, writeFile } from 'node:fs/promises';
import process from 'node:process';
import path from 'node:path';

const usage = 'Usage: node packages/tf-compose/bin/tf-manifest.mjs <flow.tf> [-o out.json]';

async function main(argv) {
  const args = argv.slice(2);
  let flowPath;
  let outPath;

  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '-o') {
      if (i + 1 >= args.length) {
        throw new Error('-o requires a file path');
      }
      outPath = args[i + 1];
      i += 1;
    } else if (!flowPath) {
      flowPath = arg;
    } else {
      throw new Error(`Unexpected argument: ${arg}`);
    }
  }

  if (!flowPath) {
    throw new Error('Missing flow path');
  }

  const [{ parseDSL }, { checkIR }, { manifestFromVerdict }] = await Promise.all([
    import('../src/parser.mjs'),
    import('../../tf-l0-check/src/check.mjs'),
    import('../../tf-l0-check/src/manifest.mjs')
  ]);

  const flowSource = await readFile(flowPath, 'utf8');
  const ir = parseDSL(flowSource);

  const catalogPath = path.resolve('packages/tf-l0-spec/spec/catalog.json');
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
