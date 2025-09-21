#!/usr/bin/env node
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { fromJSON, toJSON, unify } from '../packages/tf-l0-types/src/types.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(__dirname, '..');
const SPEC_PATH = resolve(ROOT, 'packages/tf-l0-spec/spec/signatures.demo.json');
const OUT_PATH = resolve(ROOT, 'out/0.4/check/types-demo.json');

const CHAINS = [
  { name: 'hash|>hash', steps: ['tf:information/hash@1', 'tf:information/hash@1'] },
  { name: 'publish|>emit-metric', steps: ['tf:network/publish@1', 'tf:observability/emit-metric@1'] },
  { name: 'write-object|>publish', steps: ['tf:resource/write-object@1', 'tf:network/publish@1'] }
];

const spec = loadSpec(SPEC_PATH);
const results = CHAINS.map((chain) => evaluateChain(chain, spec));
const summary = results.reduce(
  (acc, entry) => {
    if (entry.ok) {
      acc.ok += 1;
    } else {
      acc.fail += 1;
    }
    return acc;
  },
  { ok: 0, fail: 0 }
);

writeCanonicalJSON(OUT_PATH, { cases: results, summary });

function loadSpec(path) {
  const raw = JSON.parse(readFileSync(path, 'utf8'));
  const catalog = new Map();
  for (const [id, entry] of Object.entries(raw)) {
    if (!entry || typeof entry !== 'object') {
      throw new TypeError(`Invalid spec entry for ${id}`);
    }
    const input = fromJSON(entry.input);
    const output = fromJSON(entry.output);
    catalog.set(id, { input, output });
  }
  return catalog;
}

function evaluateChain(chain, catalog) {
  const steps = chain.steps;
  for (const id of steps) {
    if (!catalog.has(id)) {
      throw new Error(`Unknown primitive in chain ${chain.name}: ${id}`);
    }
  }
  for (let i = 0; i < steps.length - 1; i += 1) {
    const left = catalog.get(steps[i]);
    const right = catalog.get(steps[i + 1]);
    const verdict = unify(left.output, right.input);
    if (!verdict.ok) {
      return { chain: chain.name, ok: false, reason: verdict.reason };
    }
  }
  const last = catalog.get(steps[steps.length - 1]);
  return { chain: chain.name, ok: true, type: toJSON(last.output) };
}

function writeCanonicalJSON(path, value) {
  mkdirSync(dirname(path), { recursive: true });
  const canonical = canonicalize(value);
  const text = `${JSON.stringify(canonical, null, 2)}\n`;
  writeFileSync(path, text);
}

function canonicalize(value) {
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  if (value && typeof value === 'object') {
    const result = {};
    for (const key of Object.keys(value).sort()) {
      result[key] = canonicalize(value[key]);
    }
    return result;
  }
  return value;
}
