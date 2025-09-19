import { mkdirSync, readdirSync, copyFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const root = dirname(here);
const srcDir = join(root, 'src', 'schemas');
const distDir = join(root, 'dist', 'schemas');

mkdirSync(distDir, { recursive: true });
for (const entry of readdirSync(srcDir)) {
  if (!entry.endsWith('.json')) {
    continue;
  }
  copyFileSync(join(srcDir, entry), join(distDir, entry));
}
