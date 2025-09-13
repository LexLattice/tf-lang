
import { blake3 } from '@noble/hashes/blake3';
import { utf8ToBytes } from '@noble/hashes/utils';
import type { Filters } from './types.js';

export function queryHash(obj: Filters): string {
  const s = JSON.stringify(obj, Object.keys(obj).sort());
  return Buffer.from(blake3(utf8ToBytes(s))).toString('hex');
}
