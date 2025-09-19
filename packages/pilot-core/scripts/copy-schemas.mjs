import { mkdir, cp } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const root = resolve(__dirname, '..');
const srcDir = resolve(root, 'src/schemas');
const outDir = resolve(root, 'schemas');

await mkdir(outDir, { recursive: true });
await cp(srcDir, outDir, { recursive: true });
