
import { blake3 } from '@noble/hashes/blake3';
import { bytesToHex } from '@noble/hashes/utils';

export function queryHash(obj: Record<string, unknown>): string {
  const s = JSON.stringify(obj, Object.keys(obj).sort());
  const bytes = new TextEncoder().encode(s);
  return bytesToHex(blake3(bytes));
}
