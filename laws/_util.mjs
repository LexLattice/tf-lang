export function ensurePublishNodes({ publishNodes = [], nodes = [] } = {}) {
  if (Array.isArray(publishNodes) && publishNodes.length > 0) {
    return publishNodes.map((entry) => (entry && entry.node ? entry : { node: entry }));
  }
  if (!Array.isArray(nodes)) return [];
  return nodes
    .filter((n) => n && typeof n === 'object' && n.kind === 'Publish')
    .map((node) => ({ node }));
}
