import { readFileSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import { mkdirSync } from 'node:fs';

import { Frame, canonFrame } from '@tf-lang/pilot-core';

export interface ReplayOptions {
  input: string;
  seed: number;
  slice?: string;
}

export interface ReplayResult {
  frames: Frame[];
}

export function loadCsvFrames(filePath: string): Frame[] {
  const content = readFileSync(filePath, 'utf-8');
  const lines = content
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
  if (lines.length === 0) {
    return [];
  }
  const [header, ...rows] = lines;
  const columns = header.split(',').map((value) => value.trim());
  const expected = ['ts', 'sym', 'bid', 'ask', 'last', 'volume'];
  if (JSON.stringify(columns) !== JSON.stringify(expected)) {
    throw new Error(`Unexpected CSV header: ${header}`);
  }
  let seq = 0;
  const frames = rows.map((row) => {
    const parts = row.split(',').map((value) => value.trim());
    if (parts.length !== expected.length) {
      throw new Error(`Invalid CSV row: ${row}`);
    }
    const [ts, sym, bid, ask, last, volume] = parts;
    const canonical = canonFrame({
      ts: Number(ts),
      sym,
      seq: seq++,
      bid,
      ask,
      last,
      volume,
      meta: { source: 'csv' },
    });
    return canonical;
  });
  return sortFrames(frames);
}

export function applySlice(frames: Frame[], slice?: string): Frame[] {
  if (!slice) {
    return frames;
  }
  const [startStr, endStr, stepStr] = slice.split(':');
  const start = startStr ? Number(startStr) : 0;
  const end = endStr ? Number(endStr) : frames.length;
  const step = stepStr ? Number(stepStr) : 1;
  if (!Number.isInteger(start) || !Number.isInteger(end) || !Number.isInteger(step)) {
    throw new Error('Slice values must be integers');
  }
  if (step <= 0) {
    throw new Error('Slice step must be positive');
  }
  const result: Frame[] = [];
  for (let i = Math.max(0, start); i < Math.min(end, frames.length); i += step) {
    result.push(frames[i]);
  }
  return result;
}

export function replay(options: ReplayOptions): ReplayResult {
  const frames = applySlice(loadCsvFrames(options.input), options.slice);
  return { frames };
}

export function writeFramesNdjson(outPath: string, frames: Frame[]): void {
  const directory = dirname(outPath);
  mkdirSync(directory, { recursive: true });
  const content = frames.map((frame) => JSON.stringify(frame)).join('\n');
  writeFileSync(outPath, content + (frames.length ? '\n' : ''));
}

function sortFrames(frames: Frame[]): Frame[] {
  return [...frames].sort((a, b) => {
    if (a.ts !== b.ts) {
      return a.ts - b.ts;
    }
    if (a.sym < b.sym) {
      return -1;
    }
    if (a.sym > b.sym) {
      return 1;
    }
    return a.seq - b.seq;
  });
}
