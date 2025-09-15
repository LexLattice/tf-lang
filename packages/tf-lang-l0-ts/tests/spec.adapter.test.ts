import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { describe, it, expect } from 'vitest';
import { parseSpec, canonicalSpec, serializeSpec } from '../src/spec/adapter.js';
import { canonicalJsonBytes } from '../src/canon/json.js';

const td = new TextDecoder();

function exampleDir() {
  return join(__dirname, '../../..', 'examples/specs');
}

describe('tf-spec adapter', () => {
  const dir = exampleDir();
  for (const file of readdirSync(dir)) {
    if (!file.endsWith('.json')) continue;
    it(`round-trips ${file}`, () => {
      const json = readFileSync(join(dir, file), 'utf8');
      const original = JSON.parse(json);
      const spec = canonicalSpec(parseSpec(original));
      const canon = serializeSpec(spec);
      const origCanon = canonicalJsonBytes(original);
      expect(td.decode(canon)).toBe(td.decode(origCanon));
    });
  }
});
