import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';

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

export interface CommonCliFlags {
  seed: number;
  slice?: string;
  outPath?: string;
  outDir?: string;
  force: boolean;
  rest: string[];
}

interface ParseCommonFlagsOptions {
  requireSeed?: boolean;
  requireOut?: boolean;
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
    ok: true,
    seed: options.seed,
    slice: options.slice,
    files,
  };
  const serialised = JSON.stringify(payload, null, 2) + '\n';
  writeFileSync(options.outPath, serialised, 'utf-8');
}

export function parseCommonFlags(args: string[], options: ParseCommonFlagsOptions = {}): CommonCliFlags {
  const rest: string[] = [];
  let seed: number | undefined;
  let slice: string | undefined;
  let outPath: string | undefined;
  let outDir: string | undefined;
  let force = false;

  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    switch (arg) {
      case '--seed': {
        const next = args[++i];
        if (next === undefined) {
          throw new Error('Missing value for --seed');
        }
        const parsed = Number(next);
        if (!Number.isFinite(parsed)) {
          throw new Error('Seed must be a finite number');
        }
        seed = parsed;
        break;
      }
      case '--slice': {
        const next = args[++i];
        if (next === undefined) {
          throw new Error('Missing value for --slice');
        }
        slice = next;
        break;
      }
      case '--out': {
        const next = args[++i];
        if (next === undefined) {
          throw new Error('Missing value for --out');
        }
        outPath = next;
        break;
      }
      case '--out-dir': {
        const next = args[++i];
        if (next === undefined) {
          throw new Error('Missing value for --out-dir');
        }
        outDir = next;
        break;
      }
      case '--force':
        force = true;
        break;
      default:
        rest.push(arg);
    }
  }

  if (options.requireSeed !== false && seed === undefined) {
    throw new Error('Missing required --seed flag');
  }
  if (options.requireOut !== false && !outPath && !outDir) {
    throw new Error('Missing required output flag (--out or --out-dir)');
  }

  if (outPath) {
    ensureWritableFile(outPath, force);
  }
  if (outDir) {
    mkdirSync(resolve(outDir), { recursive: true });
  }

  return {
    seed: seed ?? 0,
    slice,
    outPath,
    outDir,
    force,
    rest,
  };
}

export function ensureWritableFile(path: string, force: boolean): void {
  const absolute = resolve(path);
  const directory = dirname(absolute);
  mkdirSync(directory, { recursive: true });
  if (!force && existsSync(absolute)) {
    throw new Error(`Output file already exists: ${absolute} (use --force to overwrite)`);
  }
}
