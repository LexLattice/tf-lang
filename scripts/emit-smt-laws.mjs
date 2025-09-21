#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname, extname, resolve } from 'node:path';
import process from 'node:process';
import { parseArgs } from 'node:util';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import {
  emitLaw,
  emitFlowEquivalence
} from '../packages/tf-l0-proofs/src/smt-laws.mjs';

async function main(argv) {
  const { values, positionals } = parseArgs({
    args: argv.slice(2),
    options: {
      law: { type: 'string' },
      equiv: { type: 'boolean' },
      laws: { type: 'string' },
      out: { type: 'string', short: 'o' }
    },
    allowPositionals: true
  });

  const modeLaw = typeof values.law === 'string';
  const modeEquiv = Boolean(values.equiv);

  if (modeLaw === modeEquiv) {
    usage();
    process.exit(1);
  }

  if (modeLaw) {
    const outArg = values.out ?? defaultLawOut(values.law);
    const outPath = resolve(outArg);
    await mkdir(dirname(outPath), { recursive: true });
    const smt = emitLaw(values.law);
    await writeFile(outPath, smt, 'utf8');
    process.stdout.write(`wrote ${outPath}\n`);
    return;
  }

  if (positionals.length !== 2) {
    usage();
    process.exit(1);
  }

  const [flowAPath, flowBPath] = positionals.map((p) => resolve(p));
  const [srcA, srcB] = await Promise.all([
    readFile(flowAPath, 'utf8'),
    readFile(flowBPath, 'utf8')
  ]);
  const [irA, irB] = [parseDSL(srcA), parseDSL(srcB)];
  const lawSet = parseLaws(values.laws);
  const smt = emitFlowEquivalence(irA, irB, lawSet);
  const outArg = values.out ?? defaultEquivOut(flowAPath, flowBPath);
  const outPath = resolve(outArg);
  await mkdir(dirname(outPath), { recursive: true });
  await writeFile(outPath, smt, 'utf8');
  process.stdout.write(`wrote ${outPath}\n`);
}

function usage() {
  process.stderr.write(
    'Usage:\n' +
      '  node scripts/emit-smt-laws.mjs --law <law> -o <out.smt2>\n' +
      '  node scripts/emit-smt-laws.mjs --equiv <flowA.tf> <flowB.tf> --laws <law1,law2> -o <out.smt2>\n'
  );
}

function defaultLawOut(law) {
  const stem = (law || 'law').replace(/[^A-Za-z0-9]+/g, '_');
  return `out/0.4/proofs/laws/${stem}.smt2`;
}

function defaultEquivOut(flowAPath, flowBPath) {
  const left = stemFromPath(flowAPath);
  const right = stemFromPath(flowBPath);
  return `out/0.4/proofs/laws/${left}_vs_${right}.smt2`;
}

function stemFromPath(path) {
  const base = basename(path);
  const ext = extname(base);
  return ext ? base.slice(0, -ext.length) : base;
}

function parseLaws(value) {
  if (!value) {
    return [];
  }
  return value
    .split(',')
    .map((law) => law.trim())
    .filter((law) => law.length > 0);
}

main(process.argv).catch((err) => {
  process.stderr.write(String(err?.stack || err));
  process.stderr.write('\n');
  process.exit(1);
});
