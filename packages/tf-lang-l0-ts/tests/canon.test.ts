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

  it('blake3 hex', () => {
    const hex = blake3hex(new Uint8Array());
    expect(hex).toBe('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262');
  });
});

