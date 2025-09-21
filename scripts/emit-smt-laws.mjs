#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { emitLaw, emitFlowEquivalence } from '../packages/tf-l0-proofs/src/smt-laws.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      law: { type: 'string' },
      equiv: { type: 'string' },
      laws: { type: 'string' },
      out: { type: 'string', short: 'o' },
    },
    allowPositionals: true,
  });

  const outPath = typeof values.out === 'string' ? resolve(values.out) : null;
  if (!outPath) {
    usage('missing --out <file>');
    process.exit(2);
  }

  const lawName = values.law ?? null;
  const flowPaths = [];
  if (typeof values.equiv === 'string') {
    flowPaths.push(values.equiv);
  }
  flowPaths.push(...positionals);

  if (lawName && flowPaths.length > 0) {
    usage('use either --law or --equiv, not both');
    process.exit(2);
  }

  if (lawName) {
    const smt = emitLaw(lawName);
    await writeOutput(outPath, smt);
    process.stdout.write(`wrote ${outPath}\n`);
    return;
  }

  if (flowPaths.length !== 2) {
    usage('expected --equiv <flowA> <flowB>');
    process.exit(2);
  }

  const [left, right] = await Promise.all(flowPaths.map((entry) => loadFlow(entry)));

  const laws = parseLawList(values.laws);
  const smt = emitFlowEquivalence(left, right, laws);
  await writeOutput(outPath, smt);
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage(message) {
  if (message) {
    process.stderr.write(`${message}\n`);
  }
  process.stderr.write(
    'Usage:\n' +
      '  node scripts/emit-smt-laws.mjs --law <name> -o <out.smt2>\n' +
      '  node scripts/emit-smt-laws.mjs --equiv <flowA> <flowB> --laws a,b -o <out.smt2>\n'
  );
}

async function loadFlow(source) {
  const resolved = resolve(source);
  try {
    const raw = await readFile(resolved, 'utf8');
    return parseFlow(raw);
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      return parseFlow(source);
    }
    throw error;
  }
}

function parseFlow(source) {
  return source
    .split('|>')
    .map((segment) => segment.trim())
    .filter((segment) => segment.length > 0);
}

function parseLawList(raw) {
  if (typeof raw !== 'string' || raw.trim().length === 0) {
    return [];
  }
  return raw
    .split(',')
    .map((entry) => entry.trim())
    .filter((entry) => entry.length > 0);
}

async function writeOutput(filePath, content) {
  await mkdir(dirname(filePath), { recursive: true });
  await writeFile(filePath, ensureTrailingNewline(content), 'utf8');
}

function ensureTrailingNewline(text) {
  if (text.endsWith('\n')) {
    return text;
  }
  return `${text}\n`;
}

main(process.argv).catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
