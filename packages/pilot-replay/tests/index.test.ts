// @tf-test kind=product area=pilot speed=fast deps=node

import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';

import { describe, expect, it, vi } from 'vitest';
import { Frame } from '@tf-lang/pilot-core';

import { replay, loadCsvFrames, applySlice, writeFramesNdjson } from '../src/index.js';
import { runCli } from '../src/cli.js';

const input = fileURLToPath(new URL('../../../tests/data/ticks-mini.csv', import.meta.url));

describe('pilot-replay', () => {
  it('loads and sorts frames deterministically', () => {
    const frames = loadCsvFrames(input);
    expect(frames[0].ts).toBe(1710000000000);
    expect(frames[0].bid).toBe('65000.1');
    expect(frames[frames.length - 1].seq).toBe(frames.length - 1);
  });

  it('applies slices correctly', () => {
    const frames = loadCsvFrames(input);
    const sliced = applySlice(frames, '0:3:2');
    expect(sliced.length).toBe(2);
    expect(sliced[0].seq).toBe(0);
    expect(sliced[1].seq).toBe(2);
  });

  it('replays frames using canonical pipeline', () => {
    const result = replay({ input, seed: 42, slice: '0:5:1' });
    expect(result.frames).toHaveLength(5);
    expect(result.frames[0].sym).toBe('BTCUSDT');
  });

  it('produces identical NDJSON across runs with the same seed', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-replay-ndjson-'));
    const outA = join(base, 'frames-a.ndjson');
    const outB = join(base, 'frames-b.ndjson');
    const options = { input, seed: 42, slice: '0:5:1' } as const;
    writeFramesNdjson(outA, replay(options).frames);
    writeFramesNdjson(outB, replay(options).frames);
    const first = readFileSync(outA, 'utf-8');
    const second = readFileSync(outB, 'utf-8');
    expect(second).toBe(first);
    rmSync(base, { recursive: true, force: true });
  });

  it('fails fast when frames violate the schema', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-replay-invalid-'));
    const outPath = join(base, 'frames.ndjson');
    const invalidFrame = {
      ts: 1,
      sym: '',
      seq: 0,
      bid: '65000.1',
      ask: '65000.2',
      last: '65000.15',
      volume: '1',
    } as Frame;
    expect(() => writeFramesNdjson(outPath, [invalidFrame])).toThrow(/Frame validation failed/);
    rmSync(base, { recursive: true, force: true });
  });

  it('refuses to overwrite outputs without --force', () => {
    const base = mkdtempSync(join(tmpdir(), 'pilot-replay-cli-'));
    const outPath = join(base, 'frames.ndjson');
    writeFileSync(outPath, 'existing');
    const errorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    const code = runCli([
      'replay',
      '--input',
      input,
      '--seed',
      '42',
      '--slice',
      '0:2:1',
      '--out',
      outPath,
    ]);
    expect(code).toBe(1);
    errorSpy.mockRestore();
    rmSync(base, { recursive: true, force: true });
  });
});
