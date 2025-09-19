import { promises as fs } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { canonFrame, Frame, FrameInput } from '@tf-lang/pilot-core';

export interface SliceSpec {
  start?: number;
  end?: number;
  step?: number;
}

export interface ReplayOptions {
  input: string;
  seed?: number | string;
  slice?: SliceSpec;
}

export interface ReplayResult {
  frames: Frame[];
  meta: {
    seed?: number | string;
    input: string;
    slice?: SliceSpec;
  };
}

export async function readCsv(path: string): Promise<string> {
  const content = await fs.readFile(path, 'utf8');
  return content;
}

function parseHeader(line: string): string[] {
  return line
    .trim()
    .split(',')
    .map((part) => part.trim());
}

function parseRow(line: string, header: string[]): Record<string, string> {
  const parts = line.split(',');
  if (parts.length !== header.length) {
    throw new Error(`Malformed row: ${line}`);
  }
  const row: Record<string, string> = {};
  for (let i = 0; i < header.length; i += 1) {
    row[header[i]] = parts[i]?.trim() ?? '';
  }
  return row;
}

export interface TickRow {
  ts: string;
  sym: string;
  bid?: string;
  ask?: string;
  last?: string;
  vol?: string;
  [key: string]: string | undefined;
}

export function parseCsv(content: string): TickRow[] {
  const lines = content
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);

  if (lines.length === 0) {
    return [];
  }

  const header = parseHeader(lines[0]);
  const rows: TickRow[] = [];
  for (let i = 1; i < lines.length; i += 1) {
    const line = lines[i];
    if (line.startsWith('#')) {
      continue;
    }
    const parsed = parseRow(line, header);
    if (!parsed.ts || !parsed.sym) {
      throw new Error(`Missing ts or sym in row: ${line}`);
    }
    rows.push(parsed as TickRow);
  }
  return rows;
}

function applySlice<T>(rows: T[], slice?: SliceSpec): T[] {
  if (!slice) {
    return [...rows];
  }
  const start = slice.start ?? 0;
  const end = slice.end ?? rows.length;
  const step = slice.step ?? 1;
  if (step <= 0) {
    throw new Error('Slice step must be positive');
  }
  const result: T[] = [];
  for (let i = start; i < Math.min(end, rows.length); i += step) {
    if (i >= 0) {
      result.push(rows[i]);
    }
  }
  return result;
}

function toFrameInput(row: TickRow, index: number): FrameInput {
  const extras = Object.keys(row)
    .filter((key) => !['ts', 'sym', 'bid', 'ask', 'last', 'vol'].includes(key))
    .reduce<Record<string, string>>((acc, key) => {
      const value = row[key];
      if (value !== undefined && value !== '') {
        acc[key] = value;
      }
      return acc;
    }, {});
  return {
    ts: row.ts,
    sym: row.sym,
    seq: index,
    bid: row.bid,
    ask: row.ask,
    last: row.last,
    vol: row.vol,
    meta: Object.keys(extras).length > 0 ? extras : undefined
  };
}

function sortFrames(frames: Frame[]): Frame[] {
  return [...frames].sort((a, b) => {
    const tsDiff = BigInt(a.ts) - BigInt(b.ts);
    if (tsDiff !== BigInt(0)) {
      return tsDiff < BigInt(0) ? -1 : 1;
    }
    if (a.sym !== b.sym) {
      return a.sym < b.sym ? -1 : 1;
    }
    return a.seq - b.seq;
  });
}

export function buildFrames(rows: TickRow[]): Frame[] {
  const frames = rows.map((row, index) => canonFrame(toFrameInput(row, index)));
  return sortFrames(frames);
}

export async function replay(options: ReplayOptions): Promise<ReplayResult> {
  const absoluteInput = resolve(options.input);
  const content = await readCsv(absoluteInput);
  const rows = parseCsv(content);
  const sliced = applySlice(rows, options.slice);
  const frames = buildFrames(sliced);
  return {
    frames,
    meta: {
      seed: options.seed,
      input: absoluteInput,
      slice: options.slice
    }
  };
}

export async function writeNdjson(path: string, frames: Frame[]): Promise<void> {
  const dir = dirname(path);
  await fs.mkdir(dir, { recursive: true });
  const lines = frames.map((frame) => JSON.stringify(frame));
  await fs.writeFile(path, `${lines.join('\n')}\n`, 'utf8');
}

export function parseSlice(value: string | undefined): SliceSpec | undefined {
  if (!value) {
    return undefined;
  }
  const [start, end, step] = value.split(':');
  const spec: SliceSpec = {};
  if (start !== undefined && start.length > 0) {
    spec.start = Number(start);
  }
  if (end !== undefined && end.length > 0) {
    spec.end = Number(end);
  }
  if (step !== undefined && step.length > 0) {
    spec.step = Number(step);
  }
  return spec;
}
