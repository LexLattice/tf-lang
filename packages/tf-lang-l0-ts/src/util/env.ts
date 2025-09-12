// Centralized, cached environment feature flags for the TS runtime.
let _devProofs: boolean | undefined;
export function devProofsEnabled(): boolean {
  if (_devProofs === undefined) {
    const v = (process.env.DEV_PROOFS || '').toLowerCase();
    _devProofs = v === '1' || v === 'true';
  }
  return _devProofs;
}

// For tests only: reset the cached flag (not exported in build).
export function __resetEnvCacheForTests__() {
  _devProofs = undefined;
}
