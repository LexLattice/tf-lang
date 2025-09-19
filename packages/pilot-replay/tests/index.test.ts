import { describe, expect, it } from 'vitest';
import { buildFrames, parseCsv, parseSlice } from '../src/index.js';

describe('parseCsv', () => {
  it('reads csv content into tick rows', () => {
    const csv = 'ts,sym,bid,ask,last,vol\n1,BTCUSDT,10,11,10.5,1\n';
    const rows = parseCsv(csv);
    expect(rows).toHaveLength(1);
    expect(rows[0]).toMatchObject({ ts: '1', sym: 'BTCUSDT', bid: '10' });
  });

  it('rejects malformed rows', () => {
    const csv = 'ts,sym\n1\n';
    expect(() => parseCsv(csv)).toThrow();
  });
});

describe('buildFrames', () => {
  it('returns sorted frames', () => {
    const rows = parseCsv('ts,sym,last\n2,BTCUSDT,10\n1,BTCUSDT,9\n');
    const frames = buildFrames(rows);
    expect(frames.map((f) => f.ts)).toEqual(['1', '2']);
  });
});

describe('parseSlice', () => {
  it('parses colon-delimited values', () => {
    expect(parseSlice('0:10:2')).toEqual({ start: 0, end: 10, step: 2 });
  });
});
