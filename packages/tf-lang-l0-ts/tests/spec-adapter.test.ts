import { describe, it, expect } from 'vitest';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseSpec, serializeSpec } from '../src/spec/adapter.js';
import { canonicalJsonBytes } from '../src/canon/index.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const td = new TextDecoder();

describe('spec adapter', () => {
  const dir = path.join(__dirname, '../../../examples/specs');
  for (const file of fs.readdirSync(dir).filter(f => f.endsWith('.json'))) {
    const json = fs.readFileSync(path.join(dir, file));
    it(`round-trips ${file}`, () => {
      const spec = parseSpec(json);
      const bytes = serializeSpec(spec);
      const orig = canonicalJsonBytes(JSON.parse(td.decode(json)));
      expect(Buffer.from(bytes)).toEqual(Buffer.from(orig));
      const bytes2 = serializeSpec(spec);
      expect(Buffer.from(bytes)).toEqual(Buffer.from(bytes2));
    });
  }
});
