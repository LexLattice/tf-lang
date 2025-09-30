import { generateKeyPairSync } from 'node:crypto';
import { digestBlake3, encodeBase58 } from '../util/encoding.mjs';

export function generateKeyPairEd25519() {
  const { publicKey } = generateKeyPairSync('ed25519');
  const public_key_pem = publicKey.export({ type: 'spki', format: 'pem' }).toString();
  const digest = digestBlake3(public_key_pem);
  const key_id = `kp:${encodeBase58(digest)}`;
  // Only returning public material keeps tests deterministic without handling secrets.
  return { public_key_pem, key_id };
}

export default generateKeyPairEd25519;
