#!/usr/bin/env node
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { spawn } from 'node:child_process';

import {
  canonicalLawName,
  canonicalPrimitiveName,
  loadPrimitiveEffectMap,
} from '../../packages/tf-opt/lib/data.mjs';
import { analyzePrimitiveSequence } from '../../packages/tf-opt/lib/rewrite-detect.mjs';
import {
  emitFlowEquivalence,
  listLawNames,
} from '../../packages/tf-l0-proofs/src/smt-laws.mjs';

const KNOWN_LAW_SET = new Set(
  listLawNames().map((name) => canonicalLawName(name)).filter((name) => name.length > 0),
);

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
    .map((segment) => canonicalPrimitiveName(segment.split(/\s+/)[0]))
    .filter((segment) => segment.length > 0);
}

function reorderCommute(primitives, effectMap) {
  const reordered = [...primitives];
  if (!effectMap) {
    return reordered;
  }
  let swapped = true;
  while (swapped) {
    swapped = false;
    for (let i = 0; i < reordered.length - 1; i += 1) {
      const current = reordered[i];
      const next = reordered[i + 1];
      if (next !== 'emit-metric' || current === 'emit-metric') {
        continue;
      }
      const info = effectMap.get(current);
      if (info && info.effect === 'Pure') {
        reordered[i] = next;
        reordered[i + 1] = current;
        swapped = true;
      }
    }
  }
  return reordered;
}

async function runZ3(script) {
  return new Promise((resolve, reject) => {
    let child;
    try {
      child = spawn('z3', ['-in', '-smt2']);
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
  let source;
  try {
    source = await readFile(p, 'utf8');
  } catch (error) {
    if (error && error.code === 'ENOENT') {
      const payload = {
        ok: true,
        skipped: 'manifest not found',
        missing: [],
        linked: 0,
        used_laws: [],
      };
      console.log(JSON.stringify(payload, null, 2));
      process.exit(0);
    }
    throw error;
  }
  let raw;
  try {
    raw = JSON.parse(source);
  } catch (error) {
    console.error(`Failed to parse manifest ${p}:`, error.message);
    process.exit(1);
  }
  const missing = [];
  const normalizedUsed = [];
  const usedLawSet = new Set();
  const usedRewriteRefs = new Map();

  if (!Array.isArray(raw.used_laws)) {
    missing.push('used_laws:not-array');
  }

  if (Array.isArray(raw.used_laws)) {
    raw.used_laws.forEach((entry, index) => {
      let law = '';
      let rewriteRef = null;
      if (typeof entry === 'string') {
        law = canonicalLawName(entry);
      } else if (entry && typeof entry === 'object') {
        law = canonicalLawName(entry.law);
        if (Object.prototype.hasOwnProperty.call(entry, 'rewrite')) {
          if (typeof entry.rewrite === 'string' && entry.rewrite.trim().length > 0) {
            rewriteRef = entry.rewrite.trim();
          } else {
            missing.push(`used_laws:rewrite-invalid@${index}`);
          }
        }
      } else {
        missing.push(`used_laws:invalid-entry@${index}`);
        return;
      }
      if (!law) {
        missing.push(`used_laws:empty@${index}`);
        return;
      }
      normalizedUsed.push({ law, rewrite: rewriteRef });
      usedLawSet.add(law);
      if (rewriteRef) {
        if (usedRewriteRefs.has(rewriteRef)) {
          missing.push(`used_laws:rewrite-duplicate@${rewriteRef}`);
        } else {
          usedRewriteRefs.set(rewriteRef, law);
        }
      }
    });
  }

  normalizedUsed.forEach((entry, index) => {
    if (!KNOWN_LAW_SET.has(entry.law)) {
      missing.push(`law:unknown@used_laws[${index}]`);
    }
  });

  const usedLawList = Array.from(
    new Set(normalizedUsed.map((entry) => entry.law)),
  ).sort((a, b) => a.localeCompare(b));
  const manifestRewrites = new Map();
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
        const law = canonicalLawName(entry.law);
        const rewriteName =
          typeof entry.rewrite === 'string' && entry.rewrite.trim().length > 0
            ? entry.rewrite.trim()
            : null;
        const handle = rewriteName ?? `rewrite#${index}`;
        if (!law) {
          missing.push(`rewrite:law-missing@${handle}`);
        }
        if (!rewriteName) {
          missing.push(`rewrite:name-missing@${handle}`);
        }
        if (rewriteName) {
          if (manifestRewrites.has(rewriteName)) {
            missing.push(`rewrite:duplicate@${rewriteName}`);
          } else {
            manifestRewrites.set(rewriteName, law);
          }
        }
        if (!usedLawSet.has(law)) {
          missing.push(`rewrite:unlinked-law@${handle}`);
        }
        if (!KNOWN_LAW_SET.has(law)) {
          missing.push(`law:unknown@rewrites[${handle}]`);
        }
      });
    }
  }

  const rewriteNames = Array.from(usedRewriteRefs.keys()).sort((a, b) => a.localeCompare(b));
  if (rewriteNames.length > 0 && manifestRewrites.size === 0) {
    for (const rewriteName of rewriteNames) {
      missing.push(`rewrite:missing-entry@${rewriteName}`);
    }
  }

  for (const [rewriteName, law] of usedRewriteRefs.entries()) {
    if (!manifestRewrites.has(rewriteName)) {
      missing.push(`rewrite:missing-entry@${rewriteName}`);
      continue;
    }
    const manifestLaw = manifestRewrites.get(rewriteName);
    if (manifestLaw !== law) {
      missing.push(`rewrite:mismatched-law@${rewriteName}`);
      continue;
    }
    linked += 1;
  }

  for (const rewriteName of manifestRewrites.keys()) {
    if (!usedRewriteRefs.has(rewriteName)) {
      missing.push(`rewrite:unused-entry@${rewriteName}`);
    }
  }

  const ok = missing.length === 0;
  const result = {
    ok,
    missing: missing.sort((a, b) => a.localeCompare(b)),
    linked,
    used_laws: usedLawList,
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
  const [analysis, effectMap] = await Promise.all([
    analyzePrimitiveSequence(flow),
    loadPrimitiveEffectMap(),
  ]);
  const rewritten = reorderCommute(flow, effectMap);
  const unknown = analysis.laws.filter((law) => !KNOWN_LAW_SET.has(law));

  if (unknown.length > 0) {
    const payload = {
      ok: false,
      solver: 'tf-small-solver',
      missing_laws: unknown.sort((a, b) => a.localeCompare(b)),
      obligations: analysis.obligations,
      primitives: analysis.primitives,
      rewritten,
    };
    console.log(JSON.stringify(payload, null, 2));
    process.exit(1);
  }

  const equivalence = emitFlowEquivalence(analysis.primitives, rewritten, analysis.laws);
  const solve = await runZ3(equivalence);
  if (!solve.available) {
    const payload = {
      ok: true,
      skipped: 'z3 not found',
      solver: 'tf-small-solver',
      obligations: analysis.obligations,
      primitives: analysis.primitives,
      rewritten,
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
    rewritten,
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
