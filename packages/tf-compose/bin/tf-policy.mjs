#!/usr/bin/env node

import { mkdir, readFile, writeFile } from 'node:fs/promises';
import process from 'node:process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';

const usage = 'Usage: node packages/tf-compose/bin/tf-policy.mjs check <flow.tf> [--forbid-outside] [-o out.json]';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      'forbid-outside': { type: 'boolean' },
      out: { type: 'string', short: 'o' }
    },
    allowPositionals: true
  });

  if (positionals.length === 0) {
    throw new Error('Missing command');
  }

  const command = positionals[0];
  if (command !== 'check') {
    throw new Error(`Unknown command: ${command}`);
  }

  if (positionals.length < 2) {
    throw new Error('Missing flow path');
  }
  if (positionals.length > 2) {
    throw new Error(`Unexpected argument: ${positionals[2]}`);
  }

  const flowPath = positionals[1];
  const outPath = values.out;
  const forbidOutside = Boolean(values['forbid-outside']);

  const [{ parseDSL }, { checkTransactions }] = await Promise.all([
    import('../src/parser.mjs'),
    import('../../tf-l0-check/src/txn.mjs')
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

  const verdict = checkTransactions(ir, catalog, {
    forbidWritesOutsideTxn: forbidOutside
  });

  const payload = {
    ok: Boolean(verdict?.ok),
    reasons: [...(verdict?.reasons || [])]
  };

  const json = JSON.stringify(payload, ['ok', 'reasons']);

  if (outPath) {
    await mkdir(path.dirname(outPath), { recursive: true });
    await writeFile(outPath, `${json}\n`, 'utf8');
  } else {
    process.stdout.write(`${json}\n`);
  }

  if (!payload.ok) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  console.error(err.message || err);
  console.error(usage);
  process.exit(1);
});
