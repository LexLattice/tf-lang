import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { mkdirSync } from 'node:fs';

export interface FileSummary {
  lines: number;
  sha256: string;
}

export interface StatusFileOptions {
  seed: number;
  slice: string;
  files: Record<string, { path: string }>;
  outPath: string;
}

export function summariseFile(path: string): FileSummary {
  const absolutePath = resolve(path);
  const content = readFileSync(absolutePath);
  const sha256 = createHash('sha256').update(content).digest('hex');
  const text = content.toString('utf-8');
  const lines = text
    .split(/\r?\n/)
    .filter((line) => line.trim().length > 0)
    .length;
  return { lines, sha256 };
}

export function writeStatusFile(options: StatusFileOptions): void {
  const directory = dirname(resolve(options.outPath));
  mkdirSync(directory, { recursive: true });
  const files: Record<string, FileSummary> = {};
  for (const [name, descriptor] of Object.entries(options.files)) {
    files[name] = summariseFile(descriptor.path);
  }
  const payload = {
    seed: options.seed,
    slice: options.slice,
    files,
  };
  const serialised = JSON.stringify(payload, null, 2) + '\n';
  writeFileSync(options.outPath, serialised, 'utf-8');
}
