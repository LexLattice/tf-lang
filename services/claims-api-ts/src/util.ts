
import { blake3 } from '@noble/hashes/blake3';
import { bytesToHex } from '@noble/hashes/utils';

const te = new TextEncoder();

function canonicalBytes(obj: any): Uint8Array {
  return te.encode(JSON.stringify(obj, Object.keys(obj).sort()));
}

export function queryHash(obj: any): string {
  return bytesToHex(blake3(canonicalBytes(obj)));
}
