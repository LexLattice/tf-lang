import { describe, expect, it } from 'vitest';
import { canonFrame, canonOrder } from '@tf-lang/pilot-core';
import { createRisk } from '../src/index.js';

describe('pilot-risk', () => {
  it('passes through orders when configured', () => {
    const risk = createRisk({ mode: 'passThrough' });
    const frame = canonFrame({ ts: 1, sym: 'BTCUSDT', seq: 0, bid: '100', ask: '101', last: '100.5', volume: '1' });
    const orders = [
      canonOrder({ id: 'o-1', ts: 1, sym: 'BTCUSDT', side: 'buy', quantity: '1', price: '101' }),
    ];
    const state = { seed: 1, cash: '0', positions: {} };
    expect(risk.evaluate(state, orders, frame)).toEqual(orders);
  });

  it('rejects invalid configs', () => {
    expect(() => createRisk({} as unknown)).toThrow();
  });
});
