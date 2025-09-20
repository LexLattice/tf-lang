import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
const file = process.argv[2];
if (!file) { console.error('Usage: node hash-file.mjs <path>'); process.exit(2); }
const buf = await readFile(file);
const h = createHash('sha256').update(buf).digest('hex');
process.stdout.write(`sha256:${h}\n`);
