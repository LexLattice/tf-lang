import { ensurePublishNodes } from './_util.mjs';

const GOAL_ID = 'confidential-envelope';
const SAFE_PAYLOAD_KEYS = new Set(['envelope', 'aad', 'headers', 'metadata', 'tags']);

function hasProperty(object, key) {
  return Object.prototype.hasOwnProperty.call(object ?? {}, key);
}

function collectPlaintextPaths(payload) {
  const paths = [];
  if (!payload || typeof payload !== 'object') {
    return paths;
  }
  for (const [key, value] of Object.entries(payload)) {
    if (SAFE_PAYLOAD_KEYS.has(key)) {
      continue;
    }
    if (value !== undefined && value !== null) {
      paths.push(key);
    }
  }
  if (payload.envelope && typeof payload.envelope === 'object') {
    if (hasProperty(payload.envelope, 'plaintext')) {
      paths.push('envelope.plaintext');
    }
  }
  return paths;
}

export function checkConfidentialEnvelope(options = {}) {
  const publishEntries = ensurePublishNodes(options);
  const results = [];

  for (const entry of publishEntries) {
    const node = entry.node ?? null;
    if (!node || typeof node !== 'object') {
      continue;
    }
    const payload = node.payload && typeof node.payload === 'object' ? node.payload : null;
    const envelope = payload && typeof payload.envelope === 'object' ? payload.envelope : null;
    if (!envelope || !hasProperty(envelope, 'ciphertext')) {
      continue;
    }

    const plaintextPaths = collectPlaintextPaths(payload);
    const ciphertextRef = envelope.ciphertext ?? null;
    const ciphertextValid = typeof ciphertextRef === 'string' && ciphertextRef.length > 0;
    let status = 'PASS';
    let reason = null;
    if (!ciphertextValid) {
      status = 'WARN';
      reason = 'ciphertext-missing';
    }
    if (plaintextPaths.length > 0) {
      status = 'WARN';
      reason = 'plaintext-present';
    }
    const ok = status !== 'ERROR';

    results.push({
      goal: GOAL_ID,
      id: node.id ?? null,
      channel: typeof node.channel === 'string' ? node.channel : null,
      status,
      ok,
      satisfied: status === 'PASS',
      reason,
      plaintextPaths,
      ciphertext: ciphertextRef ?? null,
    });
  }

  const ok = results.every((entry) => entry.ok);
  return { goal: GOAL_ID, ok, results };
}

export default checkConfidentialEnvelope;
