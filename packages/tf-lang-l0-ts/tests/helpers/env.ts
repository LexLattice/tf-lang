// Scoped env override for tests to avoid leaking state across parallel cases.
import { withProofLog } from '../../src/proof/index.js';

export async function withEnv<T>(
  vars: Record<string, string | undefined>,
  fn: () => Promise<T> | T
): Promise<T> {
  const prev: Record<string, string | undefined> = {};
  const keys = Object.keys(vars);
  for (const k of keys) {
    prev[k] = process.env[k];
    const v = vars[k];
    if (v === undefined) delete process.env[k];
    else process.env[k] = v;
  }
  try {
    return await withProofLog(fn);
  } finally {
    for (const k of keys) {
      const v = prev[k];
      if (v === undefined) delete process.env[k];
      else process.env[k] = v;
    }
  }
}
