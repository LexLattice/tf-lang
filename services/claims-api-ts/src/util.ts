
import { createHash } from 'crypto';

export function queryHash(obj: any): string {
  const s = JSON.stringify(obj, Object.keys(obj).sort());
  return createHash('sha256').update(s).digest('hex');
}
