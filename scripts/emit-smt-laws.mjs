#!/usr/bin/env node
import { parseArgs } from 'node:util';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

const {
  values: { law, equiv, laws, o },
  positionals
} = parseArgs({
  options: {
    law: { type: 'string' },
    equiv: { type: 'boolean' },
    laws: { type: 'string' },
    o: { type: 'string' }
  },
  allowPositionals: true
});

if (!o) {
  throw new Error('Output path must be provided with -o');
}

if (law && equiv) {
  throw new Error('Specify either --law or --equiv, not both');
}

const outputPath = o;
await mkdir(path.dirname(outputPath), { recursive: true });

let smt;

if (law) {
  if (positionals.length > 0) {
    throw new Error('Unexpected positional arguments when using --law');
  }
  smt = emitLaw(law);
} else if (equiv) {
  if (positionals.length !== 2) {
    throw new Error('--equiv expects exactly two flow files');
  }
  const [flowAPath, flowBPath] = positionals;
  const [flowASrc, flowBSrc] = await Promise.all([
    readFile(flowAPath, 'utf8'),
    readFile(flowBPath, 'utf8')
  ]);
  const lawSet = typeof laws === 'string' && laws.length > 0 ? laws.split(',') : [];
  smt = emitFlowEquivalence(flowASrc, flowBSrc, lawSet);
} else {
  throw new Error('Either --law or --equiv must be specified');
}

await writeFile(outputPath, smt, 'utf8');
