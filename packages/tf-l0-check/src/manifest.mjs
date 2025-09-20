import { unionEffects } from './lattice.mjs';
export function manifestFromVerdict(verdict) {
  return {
    effects: verdict.effects || [],
    scopes: [],
    footprints: [...(verdict.reads||[]), ...(verdict.writes||[])]
  };
}
