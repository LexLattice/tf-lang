import { describe, it, expect } from 'vitest';
import { parseSpec, canonicalSpec, serializeSpec } from '../../src/spec/adapter.js';
import { readdirSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';

describe('tf spec adapter', () => {
  const dir = resolve(__dirname, '../../../../examples/specs');
  for (const file of readdirSync(dir)) {
    if (!file.endsWith('.json')) continue;
    it(file, () => {
      const src = readFileSync(resolve(dir, file), 'utf8');
      const parsed = parseSpec(src);
      const canon = canonicalSpec(parsed);
      const out = serializeSpec(canon);
      const parsed2 = parseSpec(out);
      expect(parsed2).toEqual(canon);
      const out2 = serializeSpec(parsed2);
      expect(out2).toBe(out);
    });
  }
});
