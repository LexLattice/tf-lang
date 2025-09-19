import { fileURLToPath } from 'node:url';

import { describe, expect, it } from 'vitest';
import { replay, loadCsvFrames, applySlice } from '../src/index.js';

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
});
