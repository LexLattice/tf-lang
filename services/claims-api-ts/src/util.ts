
import { blake3 } from '@noble/hashes/blake3';
import { utf8ToBytes } from '@noble/hashes/utils';

export function queryHash(obj: Record<string, unknown>): string {
  const keys = Object.keys(obj).sort();
  const s = JSON.stringify(obj, keys);
  return Buffer.from(blake3(utf8ToBytes(s))).toString('hex');
}
