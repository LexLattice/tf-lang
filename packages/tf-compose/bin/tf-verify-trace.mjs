#!/usr/bin/env node
import process from 'node:process';
import { parseArgs } from 'node:util';

import { verifyTrace } from '../../tf-l0-tools/verify-trace.mjs';

const usage = 'Usage: node packages/tf-compose/bin/tf-verify-trace.mjs --ir <file.ir.json> --trace <file.jsonl> [--manifest <manifest.json>] [--catalog <catalog.json>] [--status <status.json>] [--ir-hash <sha>] [--manifest-hash <sha>] [--catalog-hash <sha>]';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      ir: { type: 'string' },
      trace: { type: 'string' },
      manifest: { type: 'string' },
      catalog: { type: 'string' },
      status: { type: 'string' },
      'ir-hash': { type: 'string' },
      'manifest-hash': { type: 'string' },
      'catalog-hash': { type: 'string' },
    },
    allowPositionals: true,
  });

  if (positionals.length > 0) {
    console.error(`Unexpected argument: ${positionals[0]}`);
    console.error(usage);
    process.exitCode = 2;
    return;
  }

  if (!values.ir || !values.trace) {
    console.error('Missing required arguments');
    console.error(usage);
    process.exitCode = 2;
    return;
  }

  const { result, canonical } = await verifyTrace({
    irPath: values.ir,
    tracePath: values.trace,
    manifestPath: values.manifest,
    catalogPath: values.catalog,
    statusPath: values.status,
    irHash: values['ir-hash'],
    manifestHash: values['manifest-hash'],
    catalogHash: values['catalog-hash'],
  });

  process.stdout.write(canonical + '\n');

  if (!result.ok) {
    process.exitCode = 1;
  }
}

main(process.argv).catch((err) => {
  console.error(err?.message || err);
  console.error(usage);
  process.exitCode = 2;
});
