#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';
import { hashJsonLike } from './hash-jsonl.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const rootDir = join(here, '..');

function resolveOutDir() {
  const override = process.env.PILOT_OUT_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  return join(rootDir, 'out', '0.4', 'pilot-l0');
}

function resolveParityDir() {
  const override = process.env.PILOT_PARITY_DIR;
  if (override && override.trim()) {
    return isAbsolute(override) ? override : join(rootDir, override);
  }
  const suffix = process.env.PILOT_OUT_DIR && process.env.PILOT_OUT_DIR.trim()
    ? process.env.PILOT_OUT_DIR.replace(/[:/\\]+/g, '_')
    : null;
  return suffix
    ? join(rootDir, 'out', '0.4', 'parity', suffix)
    : join(rootDir, 'out', '0.4', 'parity');
}

const generatedDir = resolveOutDir();
const manualDir = join(generatedDir, 'manual');
const parityDir = resolveParityDir();
const reportPath = join(parityDir, 'report.json');

async function main() {
  await mkdir(parityDir, { recursive: true });

  const artifacts = [
    { name: 'status', generated: join(generatedDir, 'status.json'), manual: join(manualDir, 'status.json') },
    { name: 'trace', generated: join(generatedDir, 'trace.jsonl'), manual: join(manualDir, 'trace.jsonl') },
    { name: 'summary', generated: join(generatedDir, 'summary.json'), manual: join(manualDir, 'summary.json') },
  ];

  const report = {
    equal: true,
    diff: [],
    generated: {},
    manual: {},
  };

  for (const artifact of artifacts) {
    const generatedHash = await hashJsonLike(artifact.generated);
    const manualHash = await hashJsonLike(artifact.manual);
    report.generated[artifact.name] = generatedHash;
    report.manual[artifact.name] = manualHash;
    if (generatedHash !== manualHash) {
      report.equal = false;
      report.diff.push({
        artifact: artifact.name,
        generated: generatedHash,
        manual: manualHash,
      });
    }
  }

  await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
  if (report.equal) {
    console.log('pilot-parity: artifacts match');
  } else {
    console.warn('pilot-parity: mismatch detected');
    process.exitCode = 1;
  }
}

main().catch((err) => {
  console.error(err?.stack || err?.message || String(err));
  process.exitCode = 1;
});
