import { describe, it, expect } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import { parse, serialize } from '../src/spec/adapter';
import { canonicalize } from 'json-canonicalize';

describe('TypeScript adapter', () => {
  const examplesDir = path.resolve(__dirname, '../../../examples/specs');
  const exampleFiles = fs.readdirSync(examplesDir).filter(file => file.endsWith('.json'));

  exampleFiles.forEach(file => {
    it(`should perform round-trip conversion for ${file}`, () => {
      const filePath = path.join(examplesDir, file);
      const originalJson = fs.readFileSync(filePath, 'utf-8');
      const spec = parse(originalJson);
      const serializedJson = serialize(spec);
      const canonicalOriginal = canonicalize(JSON.parse(originalJson));

      expect(serializedJson).toEqual(canonicalOriginal);
    });
  });
});
