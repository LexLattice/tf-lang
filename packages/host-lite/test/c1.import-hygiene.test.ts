import { describe, it, expect } from 'vitest';
import { readdir, readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

async function collectTs(dir: string): Promise<string[]> {
  const entries = await readdir(dir, { withFileTypes: true });
  const files: string[] = [];
  for (const e of entries) {
    const p = join(dir, e.name);
    if (e.isDirectory()) files.push(...(await collectTs(p)));
    else if (p.endsWith('.ts')) files.push(p);
  }
  return files;
}

describe('C1: import-hygiene', () => {
  it('no deep relative cross-package imports; internal ESM imports end with .js', async () => {
    const root = fileURLToPath(new URL('..', import.meta.url));
    const files = await collectTs(root);
    for (const file of files) {
      const src = await readFile(file, 'utf8');
      const importRegex = /import\s+[^'";]+['"]([^'"]+)['"]/g;
      let m: RegExpExecArray | null;
      while ((m = importRegex.exec(src))) {
        const p = m[1];
        // no cross-package deep jumps
        expect(p.includes('../')).toBe(false);
        // no deep tf-lang-* paths
        expect(p.includes('tf-lang-l0/')).toBe(false);
        // internal relative imports must include .js
        if (p.startsWith('.')) expect(p.endsWith('.js')).toBe(true);
      }
    }
  });
});
