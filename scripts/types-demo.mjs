#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { fromJSON, toJSON, unify, toCanonicalJSON } from '../packages/tf-l0-types/src/types.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const specPath = path.resolve(__dirname, '../packages/tf-l0-spec/spec/signatures.demo.json');
const outputPath = path.resolve(__dirname, '../out/0.4/check/types-demo.json');

const specRaw = fs.readFileSync(specPath, 'utf8');
const specData = JSON.parse(specRaw);

const signatures = new Map();
for (const [id, entry] of Object.entries(specData)) {
  if (!entry.input || !entry.output) {
    throw new Error(`signature for ${id} missing input/output`);
  }
  signatures.set(id, {
    input: fromJSON(entry.input),
    output: fromJSON(entry.output),
  });
}

const chains = [
  ['tf:information/hash@1', 'tf:information/hash@1'],
  ['tf:network/publish@1', 'tf:observability/emit-metric@1'],
  ['tf:resource/read-object@1', 'tf:network/publish@1']
];

function displayName(id) {
  const afterColon = id.includes(':') ? id.split(':')[1] : id;
  const beforeAt = afterColon.includes('@') ? afterColon.split('@')[0] : afterColon;
  const parts = beforeAt.split('/');
  return parts[parts.length - 1];
}

const cases = chains.map((chain) => {
  const label = chain.map(displayName).join('|>');
  let verdict = { ok: true, type: null, reason: null };
  for (let i = 0; i < chain.length - 1; i += 1) {
    const current = signatures.get(chain[i]);
    const next = signatures.get(chain[i + 1]);
    if (!current || !next) {
      throw new Error(`unknown primitive in chain ${label}`);
    }
    const result = unify(current.output, next.input);
    if (!result.ok) {
      verdict = { ok: false, reason: result.reason, type: null };
      break;
    }
    verdict = { ok: true, reason: null, type: result.type };
  }
  if (verdict.ok && verdict.type) {
    return { chain: label, ok: true, type: toJSON(verdict.type) };
  }
  return { chain: label, ok: false, reason: verdict.reason };
});

cases.sort((a, b) => a.chain.localeCompare(b.chain));

const summary = cases.reduce(
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

const payload = { cases, summary };

fs.mkdirSync(path.dirname(outputPath), { recursive: true });
fs.writeFileSync(outputPath, `${toCanonicalJSON(payload)}\n`);
