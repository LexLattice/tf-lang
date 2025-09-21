#!/usr/bin/env node
import { mkdirSync, writeFileSync } from 'node:fs';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';
import { canonicalStringify, hashJsonFile } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const workdir = process.env.TF_PILOT_WORKDIR;
const outRoot = workdir
  ? (isAbsolute(workdir) ? workdir : join(root, workdir))
  : join(root, 'out', '0.4');
const pilotDir = join(outRoot, 'pilot-l0');
const manualDir = join(pilotDir, 'manual');
const parityDir = join(outRoot, 'parity');

mkdirSync(parityDir, { recursive: true });

const artifacts = [
  { name: 'status', path: join(pilotDir, 'status.json'), manual: join(manualDir, 'status.json'), jsonl: false },
  { name: 'trace', path: join(pilotDir, 'trace.jsonl'), manual: join(manualDir, 'trace.jsonl'), jsonl: true },
  { name: 'summary', path: join(pilotDir, 'summary.json'), manual: join(manualDir, 'summary.json'), jsonl: false },
];

const generated = {};
const manual = {};
const diff = [];

for (const artifact of artifacts) {
  const gen = hashJsonFile(artifact.path, { jsonl: artifact.jsonl });
  const man = hashJsonFile(artifact.manual, { jsonl: artifact.jsonl });
  generated[artifact.name] = gen;
  manual[artifact.name] = man;
  if (gen !== man) {
    diff.push({ artifact: artifact.name, generated: gen, manual: man });
  }
}

const report = {
  equal: diff.length === 0,
  diff,
  generated,
  manual,
};

const reportPath = join(parityDir, 'report.json');
writeFileSync(reportPath, canonicalStringify(report) + '\n', 'utf8');

if (report.equal) {
  console.log('pilot-parity: artifacts match');
  process.exit(0);
}

console.error('pilot-parity: mismatch detected');
process.exit(1);
