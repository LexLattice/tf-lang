import { canonicalJsonBytes } from '../canon/json.js';

const td = new TextDecoder();

export interface TfSpec {
  tf: string;
  args: unknown[];
  note?: string;
}

export function parseSpec(text: string): TfSpec {
  return JSON.parse(text) as TfSpec;
}

export function canonicalSpec(spec: TfSpec): TfSpec {
  return JSON.parse(td.decode(canonicalJsonBytes(spec))) as TfSpec;
}

export function serializeSpec(spec: TfSpec): string {
  return td.decode(canonicalJsonBytes(spec));
}
