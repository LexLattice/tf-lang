import { canonicalJsonBytes } from '../canon/index.js';

export interface Step {
  type: 'echo';
  message: string;
}

export interface Spec {
  version: number;
  description?: string;
  steps: Step[];
}

export function parseSpec(input: string | Uint8Array): Spec {
  const text = typeof input === 'string' ? input : new TextDecoder().decode(input);
  const data = JSON.parse(text);
  if (data.version !== 1) throw new Error('E_SPEC_VERSION');
  if (!Array.isArray(data.steps)) throw new Error('E_SPEC_STEPS');
  const steps: Step[] = [];
  for (const s of data.steps) {
    if (!s || typeof s.type !== 'string') throw new Error('E_SPEC_STEP');
    if (s.type !== 'echo' || typeof s.message !== 'string') throw new Error('E_SPEC_STEP');
    steps.push({ type: 'echo', message: s.message });
  }
  const spec: Spec = { version: 1, steps };
  if (typeof data.description === 'string') spec.description = data.description;
  return spec;
}

export function serializeSpec(spec: Spec): Uint8Array {
  return canonicalJsonBytes(spec);
}
