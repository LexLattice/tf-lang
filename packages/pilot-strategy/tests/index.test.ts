import { describe, expect, it } from 'vitest';
import { Frame, canonFrame, validateOrder } from '@tf-lang/pilot-core';
import { STRATEGY_DEFAULTS, createStrategy, runStrategy } from '../src/index.js';

function sampleFrames(): Frame[] {
  return [
    canonFrame({ ts: 1, sym: 'BTCUSDT', seq: 0, bid: '100', ask: '101', last: '100.5', volume: '1' }),
    canonFrame({ ts: 2, sym: 'BTCUSDT', seq: 1, bid: '100.2', ask: '101.2', last: '100.7', volume: '1' }),
    canonFrame({ ts: 3, sym: 'BTCUSDT', seq: 2, bid: '100.4', ask: '101.4', last: '100.9', volume: '1' }),
    canonFrame({ ts: 4, sym: 'BTCUSDT', seq: 3, bid: '100.6', ask: '101.6', last: '101.1', volume: '1' }),
    canonFrame({ ts: 5, sym: 'BTCUSDT', seq: 4, bid: '100.3', ask: '101.3', last: '100.4', volume: '1' }),
    canonFrame({ ts: 6, sym: 'BTCUSDT', seq: 5, bid: '100.1', ask: '101.1', last: '100.0', volume: '1' }),
    canonFrame({ ts: 7, sym: 'BTCUSDT', seq: 6, bid: '99.9', ask: '100.9', last: '99.6', volume: '1' }),
    canonFrame({ ts: 8, sym: 'BTCUSDT', seq: 7, bid: '100.0', ask: '101.0', last: '100.2', volume: '1' })
  ];
}

describe('pilot-strategy', () => {
  it('momentum strategy emits breakout orders deterministically', () => {
    const strategy = createStrategy('momentum', { seed: 42 });
    const frames = sampleFrames();
    const state = { seed: 42, cash: '0', positions: {} };
    const orders = frames.flatMap((frame) => strategy.decide(state, frame));
    expect(orders.length).toBeGreaterThan(0);
    for (const order of orders) {
      expect(validateOrder(order)).toBe(true);
      expect(order.id.startsWith('momentum-')).toBe(true);
    }
  });

  it('mean reversion strategy emits buys when price is below band', () => {
    const frames = sampleFrames();
    const { orders } = runStrategy({ strategy: 'meanReversion', framesPath: '', seed: 7 }, frames);
    const sides = new Set(orders.map((order) => order.side));
    expect(sides.has('buy')).toBe(true);
    expect(sides.has('sell')).toBe(false);
  });

  it('allows overriding defaults through parameters', () => {
    const frames = sampleFrames();
    const options = {
      strategy: 'momentum' as const,
      framesPath: '',
      seed: 11,
      parameters: { window: STRATEGY_DEFAULTS.momentum.window + 1, quantity: '2' },
    };
    const { orders } = runStrategy(options, frames);
    expect(orders.every((order) => order.quantity === '2')).toBe(true);
  });
});
