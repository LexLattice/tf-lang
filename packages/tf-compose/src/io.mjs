import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
export async function readText(p){ return await readFile(p, 'utf8'); }
export async function writeText(p, s){ await mkdir(dirname(p), { recursive:true }); await writeFile(p, s, 'utf8'); }
