import { blake3 } from '@noble/hashes/blake3';
import { utf8ToBytes } from '@noble/hashes/utils';
export function queryHash(obj) {
    const s = JSON.stringify(obj, Object.keys(obj).sort());
    return Buffer.from(blake3(utf8ToBytes(s))).toString('hex');
}
