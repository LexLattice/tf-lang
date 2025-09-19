import { describe, expect, it } from 'vitest';
import {
  assertValidFrame,
  assertValidOrder,
  assertValidState,
  canonFrame,
  canonNumber,
  canonOrder,
  seedRng,
  toMinorUnits,
} from '../src/index.js';

describe('pilot-core helpers', () => {
  it('canonicalises frames and validates', () => {
    const frame = canonFrame({
      ts: 1000,
      sym: 'BTCUSDT',
      seq: 1,
      bid: '0100.500',
      ask: 100.6,
      last: '100.55',
      volume: '0001.000',
    });
    expect(frame.bid).toBe('100.5');
    expect(frame.volume).toBe('1');
    expect(() => assertValidFrame(frame)).not.toThrow();
  });

  it('canonicalises orders', () => {
    const order = canonOrder({
      id: 'o-1',
      ts: 2000,
      sym: 'BTCUSDT',
      side: 'buy',
      quantity: '001.000',
      price: 100.5,
    });
    expect(order.quantity).toBe('1');
    expect(order.price).toBe('100.5');
    expect(() => assertValidOrder(order)).not.toThrow();
  });

  it('validates state', () => {
    expect(() =>
      assertValidState({
        seed: 42,
        cash: '1000',
        positions: {},
      }),
    ).not.toThrow();
  });

  it('produces deterministic rng output', () => {
    const rng = seedRng(42);
    expect(rng()).toBeCloseTo(0.44829055899754167, 12);
    const rng2 = seedRng('seed');
    expect(rng2()).toBeCloseTo(0.02951375348493457, 12);
  });

  it('canonicalises numbers', () => {
    expect(canonNumber('010.5000')).toBe('10.5');
    expect(canonNumber(0.1)).toBe('0.1');
  });

  it('converts to minor units respecting scale', () => {
    expect(toMinorUnits('10.5', 2)).toBe('1050');
    expect(toMinorUnits('0.005', 3)).toBe('5');
    expect(() => toMinorUnits('1.234', 2)).toThrow();
  });
});
