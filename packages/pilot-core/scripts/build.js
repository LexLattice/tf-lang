import { spawnSync } from 'node:child_process';
import { cpSync, mkdirSync, readdirSync, statSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const root = join(__dirname, '..');

const tsc = spawnSync('tsc', ['-p', join(root, 'tsconfig.json')], { stdio: 'inherit' });
if (tsc.status !== 0) {
  process.exit(tsc.status ?? 1);
}

const srcSchemas = join(root, 'src', 'schemas');
const distSchemas = join(root, 'dist', 'schemas');
mkdirSync(distSchemas, { recursive: true });

for (const entry of readdirSync(srcSchemas)) {
  const sourcePath = join(srcSchemas, entry);
  const stats = statSync(sourcePath);
  if (stats.isFile() && entry.endsWith('.json')) {
    cpSync(sourcePath, join(distSchemas, entry));
  }
}
