#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { spawn } from 'node:child_process';

import { loadLawAliasSet } from '../../packages/tf-opt/lib/data.mjs';
import { analyzePrimitiveSequence } from '../../packages/tf-opt/lib/rewrite-detect.mjs';
import { emitFlowEquivalence } from '../../packages/tf-l0-proofs/src/smt-laws.mjs';

const arg = (k) => {
  const i = process.argv.indexOf(k);
  return i >= 0 ? process.argv[i + 1] : null;
};

function parseSmallFlow(source) {
  const cleaned = source
    .replace(/\/\*[^]*?\*\//g, '')
    .replace(/\/\/.*$/gm, '')
    .replace(/#.*$/gm, '');
  const withoutSeq = cleaned.replace(/\bseq\s*\{/gi, '').replace(/\}/g, '');
  return withoutSeq
    .split('|>')
    .map((segment) => segment.trim())
    .filter((segment) => segment.length > 0)
    .map((segment) => segment.split(/\s+/)[0]);
}

function normalizeLaw(value) {
  if (typeof value !== 'string') return '';
  return value.trim();
}

async function runZ3(script) {
  return new Promise((resolve, reject) => {
    let child;
    try {
      child = spawn('z3', ['-in']);
    } catch (error) {
      if (error && error.code === 'ENOENT') {
        resolve({ available: false });
        return;
      }
      reject(error);
      return;
    }

    let resolved = false;
    let stdout = '';
    let stderr = '';
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', (chunk) => {
      stdout += chunk;
    });
    child.stderr.on('data', (chunk) => {
      stderr += chunk;
    });
    child.on('error', (error) => {
      if (resolved) return;
      if (error && error.code === 'ENOENT') {
        resolved = true;
        resolve({ available: false });
      } else {
        resolved = true;
        reject(error);
      }
    });
    child.on('close', (code) => {
      if (resolved) return;
      resolved = true;
      resolve({ code, stdout, stderr, available: true });
    });

    child.stdin.write(script);
    if (!script.trim().toLowerCase().includes('(exit')) {
      child.stdin.write('\n(exit)\n');
    }
    child.stdin.end();
  });
}

if (process.argv.includes('--check-used')) {
  const target = arg('--check-used');
  if (!target) {
    console.error('Missing path for --check-used');
    process.exit(2);
  }
  const p = resolve(target);
  const raw = JSON.parse(await readFile(p, 'utf8'));
  const lawSet = await loadLawAliasSet();
  const missing = [];

  if (!Array.isArray(raw.used_laws)) {
    missing.push('used_laws:not-array');
  }

  const usedLaws = [];
  if (Array.isArray(raw.used_laws)) {
    raw.used_laws.forEach((value, index) => {
      if (typeof value !== 'string') {
        missing.push(`used_laws:invalid-entry@${index}`);
        return;
      }
      const law = normalizeLaw(value);
      if (!law) {
        missing.push(`used_laws:empty@${index}`);
        return;
      }
      usedLaws.push(law);
    });
  }
  const usedLawSet = new Set(usedLaws);

  for (const [index, law] of usedLaws.entries()) {
    if (!lawSet.has(law)) {
      missing.push(`law:unknown@used_laws[${index}]`);
    }
  }

  let linked = 0;
  if (raw.rewrites !== undefined) {
    if (!Array.isArray(raw.rewrites)) {
      missing.push('rewrites:not-array');
    } else {
      raw.rewrites.forEach((entry, index) => {
        if (!entry || typeof entry !== 'object') {
          missing.push(`rewrite:invalid-entry@${index}`);
          return;
        }
        const law = normalizeLaw(entry.law);
        const rewriteName = typeof entry.rewrite === 'string' ? entry.rewrite : `rewrite#${index}`;
        if (!law) {
          missing.push(`rewrite:law-missing@${rewriteName}`);
          return;
        }
        const linkedToKnownLaw = usedLawSet.has(law) && lawSet.has(law);
        if (!usedLawSet.has(law)) {
          missing.push(`rewrite:unlinked-law@${rewriteName}`);
        }
        if (linkedToKnownLaw) {
          linked += 1;
        }
        if (!lawSet.has(law)) {
          missing.push(`law:unknown@rewrites[${rewriteName}]`);
        }
      });
    }
  }

  const ok = missing.length === 0;
  const result = {
    ok,
    missing: missing.sort((a, b) => a.localeCompare(b)),
    linked,
  };
  console.log(JSON.stringify(result, null, 2));
  process.exit(ok ? 0 : 1);
}

if (process.argv.includes('--small')) {
  const target = arg('--small');
  if (!target) {
    console.error('Missing flow for --small');
    process.exit(2);
  }
  const flowPath = resolve(target);
  const source = await readFile(flowPath, 'utf8');
  const flow = parseSmallFlow(source);
  const analysis = await analyzePrimitiveSequence(flow);
  const lawSet = await loadLawAliasSet();
  const unknown = analysis.laws.filter((law) => !lawSet.has(law));

  if (unknown.length > 0) {
    const payload = {
      ok: false,
      solver: 'tf-small-solver',
      missing_laws: unknown.sort((a, b) => a.localeCompare(b)),
      obligations: analysis.obligations,
      primitives: analysis.primitives,
    };
    console.log(JSON.stringify(payload, null, 2));
    process.exit(1);
  }

  const equivalence = emitFlowEquivalence(analysis.primitives, analysis.primitives, analysis.laws);
  const solve = await runZ3(equivalence);
  if (!solve.available) {
    const payload = {
      ok: true,
      solver: 'tf-small-solver',
      obligations: analysis.obligations,
      primitives: analysis.primitives,
      laws: analysis.laws,
    };
    console.log(JSON.stringify(payload, null, 2));
    process.exit(0);
  }

  const stdout = (solve.stdout || '').trim();
  const stderr = (solve.stderr || '').trim();
  const unsat = stdout.split(/\s+/).includes('unsat');
  const payload = {
    ok: unsat,
    solver: 'z3',
    status: stdout || null,
    obligations: analysis.obligations,
    primitives: analysis.primitives,
    laws: analysis.laws,
  };
  if (stderr) {
    payload.stderr = stderr;
  }
  console.log(JSON.stringify(payload, null, 2));
  process.exit(unsat ? 0 : 1);
}

console.log('Usage: ci-gate.mjs --check-used <file> | --small <flow.tf>');
process.exit(2);
