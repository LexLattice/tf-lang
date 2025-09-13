
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';

export function queryHash(obj: Record<string, unknown>): string {
  return blake3hex(canonicalJsonBytes(obj));
}
