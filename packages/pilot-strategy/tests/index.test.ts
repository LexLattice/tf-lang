import { describe, expect, it } from 'vitest';
import { FrameSchema } from '@tf-lang/pilot-core';
import { runStrategy } from '../src/index.js';

const frames = [
  FrameSchema.parse({ ts: '1', sym: 'BTCUSDT', seq: 0, last: '10' }),
  FrameSchema.parse({ ts: '2', sym: 'BTCUSDT', seq: 1, last: '11' }),
  FrameSchema.parse({ ts: '3', sym: 'BTCUSDT', seq: 2, last: '12' }),
  FrameSchema.parse({ ts: '4', sym: 'BTCUSDT', seq: 3, last: '13' }),
  FrameSchema.parse({ ts: '5', sym: 'BTCUSDT', seq: 4, last: '12.5' }),
  FrameSchema.parse({ ts: '6', sym: 'BTCUSDT', seq: 5, last: '13.5' })
];

describe('runStrategy', () => {
  it('produces deterministic orders for momentum', () => {
    const first = runStrategy({ strategy: 'momentum', frames, seed: 42 });
    const second = runStrategy({ strategy: 'momentum', frames, seed: 42 });
    expect(first.orders).toEqual(second.orders);
  });

  it('produces deterministic orders for mean reversion', () => {
    const first = runStrategy({ strategy: 'meanReversion', frames, seed: 42 });
    const second = runStrategy({ strategy: 'meanReversion', frames, seed: 42 });
    expect(first.orders).toEqual(second.orders);
  });
});
