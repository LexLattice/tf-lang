#!/usr/bin/env node
import { mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

import { parseDSL } from '../../packages/tf-compose/src/parser.mjs';
import { getKnownLawNames } from '../../packages/tf-opt/lib/data.mjs';
import { stableStringify } from '../../packages/tf-opt/lib/plan-apply.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const root = resolve(here, '..', '..');
const binPath = resolve(root, 'packages', 'tf-opt', 'bin', 'opt.mjs');
const samplePath = resolve(root, 'samples', 'd3', 'signing_commute.tf');

async function runCli(args) {
  return new Promise((resolvePromise, rejectPromise) => {
    const proc = spawn(process.execPath, [binPath, ...args], {
      stdio: ['ignore', 'pipe', 'inherit'],
    });
    let stdout = '';
    proc.stdout.on('data', (chunk) => {
      stdout += chunk.toString();
    });
    proc.on('error', (error) => {
      rejectPromise(error);
    });
    proc.on('close', (code) => {
      if (code === 0) {
        resolvePromise(stdout.trim());
      } else {
        rejectPromise(new Error(`tf-opt exited with code ${code}`));
      }
    });
  });
}

async function main() {
  const source = await readFile(samplePath, 'utf8');
  const ir = parseDSL(source);
  const tempDir = await mkdtemp(join(tmpdir(), 'tf-opt-smoke-'));
  const inputPath = join(tempDir, 'input.json');
  const appliedPath = join(tempDir, 'applied.json');
  const usedLawsPath = join(tempDir, 'used-laws.json');

  try {
    await writeFile(inputPath, `${stableStringify(ir)}\n`, 'utf8');

    const planRaw = await runCli(['--ir', inputPath, '--plan-only']);
    const plan = JSON.parse(planRaw || '{}');

    await runCli(['--ir', inputPath, '--apply', '--out', appliedPath, '--emit-used-laws', usedLawsPath]);

    const postPlanRaw = await runCli(['--ir', appliedPath, '--plan-only']);
    const postPlan = JSON.parse(postPlanRaw || '{}');

    if (
      typeof plan.rewrites_applied === 'number' &&
      typeof postPlan.rewrites_applied === 'number'
    ) {
      if (!(postPlan.rewrites_applied < plan.rewrites_applied)) {
        throw new Error('obligations did not drop after apply');
      }
    } else {
      throw new Error('plan outputs missing rewrites_applied');
    }

    const known = new Set(getKnownLawNames());
    checkKnown(plan.used_laws, known, 'plan');
    checkKnown(postPlan.used_laws, known, 'post-plan');

    const usedRaw = await readFile(usedLawsPath, 'utf8');
    const usedJson = JSON.parse(usedRaw || '{}');
    checkKnown(usedJson.used_laws, known, '--emit-used-laws');

    console.log('tf-opt smoke: ok');
  } finally {
    await rm(tempDir, { recursive: true, force: true });
  }
}

function checkKnown(candidate, known, label) {
  for (const law of Array.isArray(candidate) ? candidate : []) {
    if (!known.has(law)) {
      throw new Error(`unknown law reported by ${label}: ${law}`);
    }
  }
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
});
