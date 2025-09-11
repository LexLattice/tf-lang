import { blake3 } from '@noble/hashes/blake3.js';
import { bytesToHex } from '@noble/hashes/utils.js';

export function blake3hex(data: Uint8Array | string): string {
  const input = typeof data === 'string' ? new TextEncoder().encode(data) : data;
  return bytesToHex(blake3(input));
}

