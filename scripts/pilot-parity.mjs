#!/usr/bin/env node
import { mkdirSync, writeFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { hashFile } from './hash-jsonl.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const pilotOutRel = process.env.TF_PILOT_OUT_DIR ?? 'out/0.4/pilot-l0';
const generatedDir = join(repoRoot, pilotOutRel);
const outRoot = dirname(generatedDir);
const manualDir = join(generatedDir, 'manual');
const parityDir = join(outRoot, 'parity');
const reportPath = join(parityDir, 'report.json');

mkdirSync(parityDir, { recursive: true });

const artifacts = ['status', 'trace', 'summary'];

function pathFor(dir, key) {
  switch (key) {
    case 'status':
      return join(dir, 'status.json');
    case 'trace':
      return join(dir, 'trace.jsonl');
    case 'summary':
      return join(dir, 'summary.json');
    default:
      throw new Error(`unknown artifact ${key}`);
  }
}

function computeHashes(dir) {
  const result = {};
  for (const artifact of artifacts) {
    const target = pathFor(dir, artifact);
    result[artifact] = hashFile(target);
  }
  return result;
}

const generatedHashes = computeHashes(generatedDir);
const manualHashes = computeHashes(manualDir);

const diff = [];
for (const key of artifacts) {
  if (generatedHashes[key] !== manualHashes[key]) {
    diff.push({ artifact: key, generated: generatedHashes[key], manual: manualHashes[key] });
  }
}

const report = {
  equal: diff.length === 0,
  diff,
  generated: generatedHashes,
  manual: manualHashes,
};

writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

if (report.equal) {
  console.log('pilot parity ok');
  process.exit(0);
} else {
  console.error('pilot parity mismatch');
  process.exit(1);
}
