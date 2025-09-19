import { describe, expect, it } from 'vitest';
import { FrameSchema, OrderSchema, StateSchema } from '@tf-lang/pilot-core';
import { RiskConfigSchema, evaluate } from '../src/index.js';

const state = StateSchema.parse({ cash: '0', positions: {}, context: {} });
const frame = FrameSchema.parse({ ts: '1', sym: 'BTCUSDT', seq: 0, last: '10' });
const orders = [
  OrderSchema.parse({ id: '1', ts: '1', sym: 'BTCUSDT', side: 'buy', type: 'market', qty: '1' }),
  OrderSchema.parse({ id: '2', ts: '1', sym: 'BTCUSDT', side: 'sell', type: 'market', qty: '1' })
];

describe('Risk evaluate', () => {
  it('passes through orders by default', () => {
    expect(evaluate(state, orders, frame)).toEqual(orders);
  });

  it('honours maxOrders limit', () => {
    const limited = evaluate(state, orders, frame, { maxOrders: 1 });
    expect(limited).toHaveLength(1);
  });

  it('validates config', () => {
    expect(() => RiskConfigSchema.parse({ maxOrders: -1 })).toThrow();
  });
});
