import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
let blake3Module;
try {
  blake3Module = require('@noble/hashes/blake3');
} catch (error) {
  if (error?.code !== 'MODULE_NOT_FOUND') {
    throw error;
  }
  blake3Module = require('@noble/hashes/blake3.js');
}

const { blake3 } = blake3Module;

const textEncoder = new TextEncoder();

function isPlainObject(value) {
  if (!value || typeof value !== 'object') return false;
  if (Array.isArray(value)) return false;
  if (value instanceof Uint8Array) return false;
  if (value instanceof ArrayBuffer) return false;
  if (Buffer.isBuffer(value)) return false;
  return true;
}

function sortValue(value) {
  if (Array.isArray(value)) {
    return value.map((item) => sortValue(item));
  }
  if (isPlainObject(value)) {
    const entries = Object.keys(value).sort().map((key) => [key, sortValue(value[key])]);
    return Object.fromEntries(entries);
  }
  return value;
}

export function stableStringify(value) {
  return JSON.stringify(sortValue(value));
}

export function toBytes(value) {
  if (value instanceof Uint8Array) {
    return value;
  }
  if (Buffer.isBuffer(value)) {
    return new Uint8Array(value);
  }
  if (value instanceof ArrayBuffer) {
    return new Uint8Array(value);
  }
  if (typeof value === 'string') {
    return textEncoder.encode(value);
  }
  if (typeof value === 'number' || typeof value === 'boolean' || value == null) {
    return textEncoder.encode(String(value));
  }
  if (typeof value === 'object') {
    return textEncoder.encode(stableStringify(value));
  }
  return textEncoder.encode(String(value));
}

export function hashBlake3(value) {
  return Buffer.from(blake3(toBytes(value))).toString('hex');
}

export function digestBlake3(value) {
  return blake3(toBytes(value));
}

export function blake3DigestBytes(value) {
  return digestBlake3(value);
}

export function encodeBase58(input) {
  const bytes = input instanceof Uint8Array ? input : toBytes(input);
  if (bytes.length === 0) return '';
  const alphabet = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  let value = 0n;
  for (const byte of bytes) {
    value = (value << 8n) + BigInt(byte);
  }
  let output = '';
  while (value > 0n) {
    const remainder = Number(value % 58n);
    output = alphabet[remainder] + output;
    value = value / 58n;
  }
  let leadingZeros = 0;
  while (leadingZeros < bytes.length && bytes[leadingZeros] === 0) {
    output = '1' + output;
    leadingZeros += 1;
  }
  return output || '1';
}

