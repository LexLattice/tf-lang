
import { createHash } from 'crypto';

/** blake3 isn't in Node stdlib; SHA-256 is fine for the skeleton. Swap with blake3 native lib later. */
export function contentHash(bytes: Uint8Array | string): string {
  const buf = typeof bytes === 'string' ? Buffer.from(bytes) : Buffer.from(bytes);
  return createHash('sha256').update(buf).digest('hex');
}

export function canonicalJson(v: unknown): string {
  // NOTE: Simple stringify; replace with a canonical JSON encoder if you need byte-stability.
  return JSON.stringify(v);
}
