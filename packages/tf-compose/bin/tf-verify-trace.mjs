#!/usr/bin/env node

import process from 'node:process';
import { parseArgs } from 'node:util';

import { verifyTrace, verifyTraceToJson } from '../../tf-l0-tools/verify-trace.mjs';

const usage = 'Usage: node packages/tf-compose/bin/tf-verify-trace.mjs --ir <file.ir.json> --trace <file.jsonl> [--manifest <manifest.json>] [--catalog <catalog.json>]';

async function main(argv) {
  let parsed;
  try {
    parsed = parseArgs({
      args: argv.slice(2),
      options: {
        ir: { type: 'string' },
        trace: { type: 'string' },
        manifest: { type: 'string' },
        catalog: { type: 'string' },
      },
    });
  } catch (err) {
    console.error(err.message || err);
    console.error(usage);
    process.exit(2);
    return;
  }

  const { values } = parsed;
  if (!values.ir || !values.trace) {
    console.error('tf-verify-trace: --ir and --trace are required');
    console.error(usage);
    process.exit(2);
    return;
  }

  try {
    const result = await verifyTrace({
      irPath: values.ir,
      tracePath: values.trace,
      manifestPath: values.manifest,
      catalogPath: values.catalog,
    });
    const output = verifyTraceToJson(result);
    process.stdout.write(output + '\n');
    process.exit(result.ok ? 0 : 1);
  } catch (err) {
    console.error(err.message || err);
    process.exit(2);
  }
}

main(process.argv);
