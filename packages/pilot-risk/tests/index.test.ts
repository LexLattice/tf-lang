import { describe, expect, it } from 'vitest';
import { canonFrame, canonOrder } from '@tf-lang/pilot-core';
import { createRisk, evaluateExposure } from '../src/index.js';

describe('pilot-risk', () => {
  it('evaluates exposure metrics per symbol', () => {
    const frames = [
      canonFrame({ ts: 1, sym: 'BTCUSDT', seq: 0, bid: '100', ask: '101', last: '100', volume: '1' }),
      canonFrame({ ts: 2, sym: 'BTCUSDT', seq: 1, bid: '100', ask: '101', last: '102', volume: '1' }),
    ];
    const orders = [
      canonOrder({ id: 'o-1', ts: 1, sym: 'BTCUSDT', side: 'buy', quantity: '1', price: '101' }),
      canonOrder({ id: 'o-2', ts: 2, sym: 'BTCUSDT', side: 'sell', quantity: '0.5', price: '100.5' }),
    ];
    const risk = createRisk({ mode: 'exposure' });
    const evaluations = risk.evaluate(frames, orders);
    expect(evaluations).toHaveLength(1);
    const [evaluation] = evaluations;
    expect(evaluation.sym).toBe('BTCUSDT');
    expect(evaluation.frameCount).toBe(2);
    expect(evaluation.orderCount).toBe(2);
    expect(evaluation.grossNotional).toBe('151.25');
    expect(evaluation.netQuantity).toBe('0.5');
    expect(evaluation.maxAbsExposure).toBe('100');
  });

  it('falls back to default exposure evaluation when invoked directly', () => {
    const frames = [
      canonFrame({ ts: 1, sym: 'ETHUSDT', seq: 0, bid: '10', ask: '11', last: '10.5', volume: '1' }),
    ];
    const orders = [
      canonOrder({ id: 'e-1', ts: 1, sym: 'ETHUSDT', side: 'buy', quantity: '2', price: '11' }),
    ];
    const evaluations = evaluateExposure(frames, orders);
    expect(evaluations[0].grossNotional).toBe('22');
    expect(evaluations[0].maxAbsExposure).toBe('21');
  });

  it('rejects invalid configs', () => {
    expect(() => createRisk({} as unknown)).toThrow();
  });
});
