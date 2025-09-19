import { describe, expect, it } from 'vitest';
import { canonFrame, canonOrder } from '@tf-lang/pilot-core';
import { evaluateExposure, parseRiskConfig } from '../src/index.js';

describe('pilot-risk', () => {
  it('validates configs', () => {
    expect(() => parseRiskConfig({ mode: 'exposure' })).not.toThrow();
    expect(() => parseRiskConfig({} as unknown)).toThrow();
  });

  it('computes deterministic exposure metrics', () => {
    const frames = [
      canonFrame({ ts: 1, sym: 'BTCUSDT', seq: 0, bid: '100', ask: '100.5', last: '100.25', volume: '1' }),
      canonFrame({ ts: 2, sym: 'BTCUSDT', seq: 1, bid: '100.8', ask: '101', last: '100.9', volume: '2' }),
      canonFrame({ ts: 3, sym: 'BTCUSDT', seq: 2, bid: '99', ask: '99.5', last: '99.25', volume: '1.5' }),
    ];
    const orders = [
      canonOrder({ id: 'o-1', ts: 2, sym: 'BTCUSDT', side: 'buy', quantity: '1', price: '101' }),
      canonOrder({ id: 'o-2', ts: 3, sym: 'BTCUSDT', side: 'sell', quantity: '0.5', price: '99' }),
    ];
    const evaluations = evaluateExposure({ orders, frames });
    expect(evaluations).toHaveLength(1);
    expect(evaluations[0]).toEqual({
      sym: 'BTCUSDT',
      window: { startTs: 1, endTs: 3 },
      metrics: {
        grossNotional: '150.5',
        netQuantity: '0.5',
        maxAbsExposure: '101',
        orderCount: 2,
      },
    });
  });
});
