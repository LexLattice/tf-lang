#!/usr/bin/env node
import { mkdirSync, writeFileSync } from 'node:fs';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { hashJsonFile } from './hash-jsonl.mjs';

const __dir = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dir, '..');
const baseOutDir = process.env.TF_PILOT_OUT_DIR
  ? resolve(repoRoot, process.env.TF_PILOT_OUT_DIR)
  : join(repoRoot, 'out', '0.4', 'pilot-l0');
const generatedDir = baseOutDir;
const goldenDir = join(generatedDir, 'golden');
const manualDir = join(generatedDir, 'manual');
const parityDir = join(generatedDir, '..', '..', 'parity');

const reportPath = join(parityDir, 'report.json');

function ensureParityDir() {
  mkdirSync(parityDir, { recursive: true });
}

async function collect(path) {
  const { digest } = await hashJsonFile(path);
  return digest;
}

async function main() {
  ensureParityDir();

  const artifacts = [
    ['status', join(goldenDir, 'status.json'), join(manualDir, 'status.json'), join(generatedDir, 'status.json')],
    ['trace', join(goldenDir, 'trace.jsonl'), join(manualDir, 'trace.jsonl'), join(generatedDir, 'trace.jsonl')],
    ['summary', join(goldenDir, 'summary.json'), join(manualDir, 'summary.json'), join(generatedDir, 'summary.json')],
  ];

  const report = {
    equal: true,
    diff: [],
    generated: {},
    manual: {},
    current: {},
  };

  for (const [name, generatedPath, manualPath, currentPath] of artifacts) {
    const generatedDigest = await collect(generatedPath);
    const manualDigest = await collect(manualPath);
    report.generated[name] = generatedDigest;
    report.manual[name] = manualDigest;
    if (currentPath) {
      report.current[name] = await collect(currentPath);
    }
    if (generatedDigest !== manualDigest) {
      report.equal = false;
      report.diff.push({ artifact: name, generated: generatedDigest, manual: manualDigest });
    }
  }

  writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);

  if (!report.equal) {
    process.exitCode = 1;
  } else {
    console.log('pilot-parity equal');
  }
}

await main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
