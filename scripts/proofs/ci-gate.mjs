#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { spawn } from 'node:child_process';
import { emitFlowEquivalence, listLawNames } from '../../packages/tf-l0-proofs/src/smt-laws.mjs';

const arg = (k) => {
  const i = process.argv.indexOf(k);
  return i >= 0 ? process.argv[i + 1] : null;
};

const KNOWN_LAWS = new Set(listLawNames());

if (process.argv.includes('--check-used')) {
  const p = arg('--check-used');
  if (!p) {
    console.error('Missing path for --check-used');
    process.exit(2);
  }
  const raw = await readFile(p, 'utf8');
  const data = JSON.parse(raw);
  const used = Array.isArray(data.used_laws) ? data.used_laws : [];
  const missing = [];
  for (const entry of used) {
    if (!KNOWN_LAWS.has(entry)) {
      missing.push(entry);
    }
  }
  console.log(JSON.stringify({ ok: missing.length === 0, missing }, null, 2));
  process.exit(missing.length === 0 ? 0 : 1);
}

if (process.argv.includes('--small')) {
  const flowPath = arg('--small');
  if (!flowPath) {
    console.error('Missing flow path for --small');
    process.exit(2);
  }
  const raw = await readFile(flowPath, 'utf8');
  const flow = parseFlow(raw);
  const witness = buildCommuteWitness(flow);
  if (!witness) {
    console.log(JSON.stringify({ ok: false, reason: 'unsupported-flow' }, null, 2));
    process.exit(1);
  }
  const program = emitFlowEquivalence(witness.original, witness.reordered, [
    'commute:emit-metric-with-pure',
  ]);
  const result = await runZ3(program);
  console.log(JSON.stringify(result, null, 2));
  process.exit(result.ok ? 0 : 1);
}

console.log('Usage: ci-gate.mjs --check-used <file> | --small <flow.tf>');
process.exit(2);

function parseFlow(source) {
  const cleaned = source
    .replace(/seq\s*\{/gi, '')
    .replace(/\}/g, '')
    .split('\n')
    .map((line) => line.trim())
    .join(' ');
  return cleaned
    .split('|>')
    .map((segment) => segment.trim())
    .filter((segment) => segment.length > 0);
}

function buildCommuteWitness(flow) {
  if (flow.length !== 2) return null;
  const [a, b] = flow;
  if (a === 'hash' && b === 'emit-metric') {
    return { original: flow, reordered: [b, a] };
  }
  if (a === 'emit-metric' && b === 'hash') {
    return { original: flow, reordered: [b, a] };
  }
  return null;
}

async function runZ3(program) {
  return new Promise((resolve) => {
    let stdout = '';
    let stderr = '';
    const child = spawn('z3', ['-in', '-smt2']);
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', (chunk) => {
      stdout += chunk;
    });
    child.stderr.on('data', (chunk) => {
      stderr += chunk;
    });
    child.on('error', (error) => {
      resolve({
        ok: false,
        solver: 'z3',
        details: 'spawn-error',
        error: error.message,
        stdout: stdout.trim(),
        stderr: stderr.trim(),
        code: null,
      });
    });
    child.on('close', (code) => {
      const trimmed = stdout.trim();
      const ok = code === 0 && /^unsat$/im.test(trimmed);
      resolve({
        ok,
        solver: 'z3',
        details: ok ? 'UNSAT (flows equivalent)' : 'SAT/UNKNOWN',
        stdout: trimmed,
        stderr: stderr.trim(),
        code,
      });
    });
    child.stdin.end(program);
  });
}
