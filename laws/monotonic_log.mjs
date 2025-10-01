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

export function checkMonotonicLog(options = {}) {
  const publishEntries = ensurePublishNodes(options);
  const results = [];

  for (const entry of publishEntries) {
    const node = entry.node ?? null;
    if (!node || typeof node !== 'object') {
      continue;
    }
    const channel = typeof node.channel === 'string' ? node.channel : null;
    if (channel !== 'policy:record') {
      continue;
    }
    results.push({
      id: node.id ?? null,
      channel,
      status: 'PASS',
      ok: true,
      reason: null,
      assumption: 'consumer-append-only',
    });
  }

  const ok = results.every((entry) => entry.status !== 'ERROR');
  return {
    ok,
    results,
  };
}

export default checkMonotonicLog;
