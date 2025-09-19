import { describe, expect, it } from 'vitest';
import {
  FrameSchema,
  OrderSchema,
  StateSchema,
  canonFrame,
  canonNumber,
  seedRng,
  toMinorUnits
} from '../src/index.js';

describe('canonNumber', () => {
  it('normalises leading and trailing zeros', () => {
    expect(canonNumber('0012.3400')).toBe('12.34');
    expect(canonNumber('-0.5000')).toBe('-0.5');
    expect(canonNumber('0')).toBe('0');
  });

  it('rejects invalid values', () => {
    expect(() => canonNumber('abc')).toThrowError();
  });
});

describe('toMinorUnits', () => {
  it('converts decimals respecting scale', () => {
    expect(toMinorUnits('1.23', 2)).toEqual({ units: '123', scale: 2 });
    expect(toMinorUnits('-0.5', 3)).toEqual({ units: '-500', scale: 3 });
  });

  it('throws when fractional precision exceeds scale', () => {
    expect(() => toMinorUnits('1.234', 2)).toThrowError();
  });
});

describe('canonFrame', () => {
  it('produces a schema-valid frame', () => {
    const frame = canonFrame({
      ts: '1700000000',
      sym: 'BTCUSDT',
      seq: 1,
      bid: '1.2000',
      ask: 1.3,
      last: 1.25,
      vol: 0.5
    });
    expect(FrameSchema.parse(frame)).toEqual(frame);
  });

  it('rejects invalid sequences', () => {
    expect(() =>
      canonFrame({
        ts: '1700000000',
        sym: 'BTCUSDT',
        seq: -1
      })
    ).toThrowError();
  });
});

describe('validators', () => {
  it('accepts valid payloads', () => {
    const order = OrderSchema.parse({
      id: '1',
      ts: '1700000000',
      sym: 'BTCUSDT',
      side: 'buy',
      type: 'limit',
      qty: '1'
    });
    expect(order.id).toBe('1');

    const state = StateSchema.parse({
      cash: '1000',
      positions: {
        BTCUSDT: { qty: '1' }
      }
    });
    expect(state.cash).toBe('1000');
  });
});

describe('seedRng', () => {
  it('is deterministic for a given seed', () => {
    const rngA = seedRng(42);
    const rngB = seedRng(42);
    const valuesA = Array.from({ length: 3 }, () => rngA());
    const valuesB = Array.from({ length: 3 }, () => rngB());
    expect(valuesA).toEqual(valuesB);
  });
});
