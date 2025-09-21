#!/usr/bin/env node
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname } from 'node:path';
import { parseArgs } from 'node:util';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

function parseFlow(source) {
  return source
    .split('|>')
    .map((segment) => segment.trim())
    .filter(Boolean)
    .map((segment) => {
      const match = segment.match(/^[a-zA-Z0-9_-]+/);
      if (!match) {
        throw new Error(`Unable to parse flow segment: ${segment}`);
      }
      return match[0];
    });
}

async function main() {
  const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: {
      law: { type: 'string' },
      equiv: { type: 'string', multiple: true },
      laws: { type: 'string' },
      output: { type: 'string', short: 'o' }
    }
  });

  const lawName = values.law;
  let equivPaths = [];
  if (typeof values.equiv === 'string') {
    equivPaths = [values.equiv];
  } else if (Array.isArray(values.equiv)) {
    equivPaths = values.equiv.slice();
  }

  if (equivPaths.length === 1 && positionals.length > 0) {
    equivPaths.push(positionals[0]);
  }

  const extraPositionals = positionals.slice(equivPaths.length > 1 ? 1 : 0);
  if (extraPositionals.length > 0 && !lawName) {
    throw new Error(`Unexpected arguments: ${extraPositionals.join(', ')}`);
  }

  if (lawName && equivPaths.length > 0) {
    throw new Error('Cannot combine --law and --equiv in the same invocation');
  }

  const lawList = typeof values.laws === 'string' && values.laws.length > 0
    ? values.laws.split(',').map((item) => item.trim()).filter(Boolean)
    : [];
  const outputPath = values.output;

  if (!outputPath) {
    throw new Error('Output path is required via --output or -o');
  }

  await mkdir(dirname(outputPath), { recursive: true });

  if (lawName) {
    const body = emitLaw(lawName);
    await writeFile(outputPath, body, 'utf8');
    return;
  }

  if (equivPaths.length === 2) {
    const [aPath, bPath] = equivPaths;
    const [aSource, bSource] = await Promise.all([
      readFile(aPath, 'utf8'),
      readFile(bPath, 'utf8')
    ]);
    const flowA = parseFlow(aSource);
    const flowB = parseFlow(bSource);
    const body = emitFlowEquivalence(flowA, flowB, lawList);
    await writeFile(outputPath, body, 'utf8');
    return;
  }

  throw new Error('Must provide either --law <name> or --equiv <flowA> <flowB>');
}

main().catch((err) => {
  console.error(err.message);
  process.exitCode = 1;
});
