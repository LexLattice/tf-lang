// @tf-test kind=product area=canon speed=fast deps=node
import { describe, it, expect } from 'vitest';
import { canonicalJsonBytes, blake3hex } from '../src/canon/index.js';

const td = new TextDecoder();

describe('canonical', () => {
  it('sorts object keys and preserves arrays', () => {
    const bytes = canonicalJsonBytes({ b: 1, a: [2,1] });
    expect(td.decode(bytes)).toBe('{"a":[2,1],"b":1}');
  });

  it('rejects floats', () => {
    expect(() => canonicalJsonBytes(1.1)).toThrowError('E_L0_FLOAT');
  });

  it('normalizes -0 to 0', () => {
    expect(canonicalJsonBytes(-0)).toEqual(canonicalJsonBytes(0));
  });

  it('rejects NaN and Infinity', () => {
    expect(() => canonicalJsonBytes(NaN)).toThrowError('E_L0_FLOAT');
    expect(() => canonicalJsonBytes(Infinity)).toThrowError('E_L0_FLOAT');
  });

  it('rejects BigInt, functions, symbols', () => {
    expect(() => canonicalJsonBytes(1n)).toThrowError('E_L0_TYPE');
    expect(() => canonicalJsonBytes(() => {})).toThrowError('E_L0_TYPE');
    expect(() => canonicalJsonBytes(Symbol('x'))).toThrowError('E_L0_TYPE');
  });

  it('deeply orders object keys', () => {
    const a = { x: { b: 1, a: 2 }, y: [{ d: 4, c: 3 }] };
    const b = { y: [{ c: 3, d: 4 }], x: { a: 2, b: 1 } };
    expect(canonicalJsonBytes(a)).toEqual(canonicalJsonBytes(b));
  });

  it('blake3 hex', () => {
    const hex = blake3hex(new Uint8Array());
    expect(hex).toBe('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262');
  });
});

