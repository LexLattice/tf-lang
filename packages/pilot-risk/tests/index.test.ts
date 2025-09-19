import { describe, expect, it } from 'vitest';
import { canonFrame, canonOrder } from '@tf-lang/pilot-core';

import { createRisk, evaluateRisk } from '../src/index.js';

describe('pilot-risk', () => {
  it('passes through orders when configured', () => {
    const risk = createRisk({ mode: 'exposure' });
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

  it('computes exposure metrics deterministically', () => {
    const frames = [
      canonFrame({
        ts: 1,
        sym: 'BTCUSDT',
        seq: 0,
        bid: '100',
        ask: '101',
        last: '100.5',
        volume: '10',
      }),
      canonFrame({
        ts: 2,
        sym: 'BTCUSDT',
        seq: 1,
        bid: '100.2',
        ask: '100.8',
        last: '100.4',
        volume: '12',
      }),
    ];
    const orders = [
      canonOrder({ id: 'o-1', ts: 1, sym: 'BTCUSDT', side: 'buy', quantity: '1', price: '101' }),
      canonOrder({ id: 'o-2', ts: 2, sym: 'BTCUSDT', side: 'sell', quantity: '0.5', price: '100.2' }),
    ];
    const evaluations = evaluateRisk({ frames, orders });
    expect(evaluations).toEqual([
      {
        sym: 'BTCUSDT',
        orderCount: 2,
        grossNotional: '151.1',
        netQuantity: '0.5',
        maxAbsExposure: '100.5',
      },
    ]);
  });
});
