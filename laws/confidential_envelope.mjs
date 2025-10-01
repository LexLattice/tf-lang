function ensurePublishNodes({ publishNodes = [], nodes = [] }) {
  if (Array.isArray(publishNodes) && publishNodes.length > 0) {
    return publishNodes.map((entry) => (entry.node ? entry : { node: entry }));
  }
  if (!Array.isArray(nodes)) {
    return [];
  }
  return nodes
    .filter((node) => node && typeof node === 'object' && node.kind === 'Publish')
    .map((node) => ({ node }));
}

function hasProperty(object, key) {
  return Object.prototype.hasOwnProperty.call(object ?? {}, key);
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
    const hasPlaintext = payload ? hasProperty(payload, 'plaintext') : false;
    const satisfied = !hasPlaintext;
    const status = satisfied ? 'PASS' : 'WARN';
    results.push({
      id: node.id ?? null,
      channel: typeof node.channel === 'string' ? node.channel : null,
      status,
      ok: status !== 'ERROR',
      satisfied,
      reason: satisfied ? null : 'plaintext-present',
    });
  }

  const ok = results.every((entry) => entry.status !== 'ERROR');
  return { ok, results };
}

export default checkConfidentialEnvelope;
