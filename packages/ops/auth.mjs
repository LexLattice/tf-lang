import { stableStringify, blake3DigestBytes, encodeBase58 } from '../util/encoding.mjs';

function cloneClaims(claims) {
  if (!claims || typeof claims !== 'object') {
    return claims;
  }
  return JSON.parse(JSON.stringify(claims));
}

export function mintTokenDeterministic({ secret = '', claims = {}, alg = 'blake3' } = {}) {
  const payload = stableStringify({ secret, claims, alg });
  const digestBytes = blake3DigestBytes(payload);
  const token = `tok_${encodeBase58(digestBytes)}`;
  return { token, claims: cloneClaims(claims), alg };
}

export function checkTokenDeterministic(token, { secret = '', claims = {}, alg = 'blake3' } = {}) {
  const { token: recomputed } = mintTokenDeterministic({ secret, claims, alg });
  return token === recomputed;
}
