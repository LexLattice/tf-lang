
import { Effects } from '../model/types.js';

export function allowlist(reads: string[] = [], writes: string[] = []): Effects {
  return Effects.from(reads, writes);
}
