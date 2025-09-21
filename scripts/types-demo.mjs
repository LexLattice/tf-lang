import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { fromJSON, toJSON, unify } from '../packages/tf-l0-types/src/types.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const ROOT = path.resolve(__dirname, '..');

const SPEC_PATH = path.join(ROOT, 'packages/tf-l0-spec/spec/signatures.demo.json');
const OUT_PATH = path.join(ROOT, 'out/0.4/check/types-demo.json');

function canonicalize(value) {
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  if (value && typeof value === 'object') {
    const entries = Object.entries(value).sort(([a], [b]) => a.localeCompare(b));
    const result = {};
    for (const [key, val] of entries) {
      result[key] = canonicalize(val);
    }
    return result;
  }
  return value;
}

function stringify(value) {
  return JSON.stringify(canonicalize(value), null, 2) + '\n';
}

const specRaw = await readFile(SPEC_PATH, 'utf8');
const spec = JSON.parse(specRaw);

const operations = new Map();
for (const [id, entry] of Object.entries(spec)) {
  operations.set(id, {
    input: fromJSON(entry.input),
    output: fromJSON(entry.output),
  });
}

const labels = {
  hash: 'tf:information/hash@1',
  serialize: 'tf:data/serialize@1',
  deserialize: 'tf:data/deserialize@1',
  publish: 'tf:network/publish@1',
  'emit-metric': 'tf:observability/emit-metric@1',
  'write-object': 'tf:resource/write-object@1',
  'compare-and-swap': 'tf:resource/compare-and-swap@1',
};

const chains = [
  { name: 'hash|>hash', ops: ['hash', 'hash'] },
  { name: 'publish|>emit-metric', ops: ['publish', 'emit-metric'] },
  { name: 'write-object|>hash', ops: ['write-object', 'hash'] },
];

function evaluateChain(chain) {
  const stages = chain.ops.map((label) => {
    const id = labels[label];
    if (!id) {
      throw new Error(`unknown operation label: ${label}`);
    }
    const entry = operations.get(id);
    if (!entry) {
      throw new Error(`missing spec for ${id}`);
    }
    return { label, id, ...entry };
  });

  if (stages.length === 0) {
    return { ok: false, reason: 'empty_chain' };
  }

  let currentType = stages[0].output;
  for (let i = 1; i < stages.length; i += 1) {
    const stage = stages[i];
    const match = unify(currentType, stage.input);
    if (!match.ok) {
      return { ok: false, reason: match.reason };
    }
    const aligned = unify(match.type, stage.output);
    if (!aligned.ok) {
      return { ok: false, reason: aligned.reason };
    }
    currentType = stage.output;
  }

  return { ok: true, type: currentType };
}

const cases = chains.map((chain) => {
  const verdict = evaluateChain(chain);
  if (verdict.ok) {
    return { chain: chain.name, ok: true, type: toJSON(verdict.type) };
  }
  return { chain: chain.name, ok: false, reason: verdict.reason };
});

const summary = cases.reduce(
  (acc, entry) => {
    if (entry.ok) {
      acc.ok += 1;
    } else {
      acc.fail += 1;
    }
    return acc;
  },
  { ok: 0, fail: 0 },
);

await mkdir(path.dirname(OUT_PATH), { recursive: true });
await writeFile(OUT_PATH, stringify({ cases, summary }));

console.log(`wrote ${OUT_PATH}`);
