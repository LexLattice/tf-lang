import assert from 'node:assert/strict';

export function extractNodes(doc) {
  if (Array.isArray(doc?.nodes)) return doc.nodes;
  if (Array.isArray(doc?.monitors)) {
    return doc.monitors.flatMap((monitor) => monitor.nodes ?? []);
  }
  throw new Error('Unsupported L0 document shape');
}

export function assertKernelOnly(doc, kinds = ['Transform', 'Publish', 'Subscribe', 'Keypair']) {
  const allowed = new Set(kinds);
  const nodes = extractNodes(doc);
  for (const node of nodes) {
    assert(allowed.has(node.kind), `Unexpected kernel kind ${node.kind} on node ${node.id}`);
  }
}

export function assertRpcPairings(doc) {
  const nodes = extractNodes(doc);
  const publishes = nodes.filter((node) => node.kind === 'Publish' && typeof node.channel === 'string' && node.channel.startsWith('rpc:req:'));
  assert(publishes.length > 0, 'No rpc:req publishes found');
  const subscribes = nodes.filter((node) => node.kind === 'Subscribe');
  for (const publish of publishes) {
    const payload = publish.payload ?? {};
    assert(Object.prototype.hasOwnProperty.call(payload, 'corr'), `RPC publish ${publish.id} missing corr`);
    assert(Object.prototype.hasOwnProperty.call(payload, 'reply_to'), `RPC publish ${publish.id} missing reply_to`);
    const { corr: corrRef, reply_to: replyTo } = payload;
    const hasMatch = subscribes.some((sub) => sub.channel === replyTo && sub.filter === corrRef);
    assert(hasMatch, `RPC publish ${publish.id} lacks matching subscribe for ${replyTo}`);
  }
}

export function assertNoPiiInMetricTags(doc, banned = ['name', 'email', 'phone']) {
  const nodes = extractNodes(doc);
  const metrics = nodes.filter((node) => node.kind === 'Publish' && typeof node.channel === 'string' && node.channel.startsWith('metric:'));
  assert(metrics.length > 0, 'No metric publishes found');
  const forbidden = new Set(banned.map((key) => key.toLowerCase()));
  for (const publish of metrics) {
    const tags = publish.payload?.tags ?? {};
    for (const key of Object.keys(tags)) {
      assert(!forbidden.has(key.toLowerCase()), `Metric ${publish.id} contains forbidden tag key: ${key}`);
    }
  }
}
