import type { ProofTag } from './tags.js';
import { DEV_PROOFS } from './flag.js';
import { emit as collect } from './log.js';

const TRACE_STDOUT = process.env.TF_TRACE_STDOUT === '1';

export type ProofMeta = {
  runtime: 'ts';
  ts: number;
  region?: string;
  gate?: string;
  oracle?: string;
  seed?: number | string;
};

export function emitTag(tag: ProofTag, meta: ProofMeta): void {
  if (!DEV_PROOFS) return;
  if (TRACE_STDOUT) {
    const line = JSON.stringify({ ...meta, tag }) + '\n';
    process.stdout.write(line);
  }
  collect(tag);
}
