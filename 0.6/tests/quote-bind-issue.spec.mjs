#!/usr/bin/env node
import fs from 'node:fs';
import process from 'node:process';

function fail(msg) {
  console.error('FAIL:', msg);
  process.exit(1);
}

function ok(msg) {
  console.log('OK  :', msg);
}

const argIndex = process.argv.indexOf('--l0');
if (argIndex < 0 || argIndex + 1 >= process.argv.length) fail('Missing --l0 <path>');
const l0Path = process.argv[argIndex + 1];
const doc = JSON.parse(fs.readFileSync(l0Path, 'utf8'));

const rpcPublishes = doc.nodes.filter((n) => n.kind === 'Publish' && typeof n.channel === 'string' && n.channel.startsWith('rpc:req:'));
const subscribes = doc.nodes.filter((n) => n.kind === 'Subscribe');
if (rpcPublishes.length === 0) fail('No rpc:req publishes found');
for (const node of rpcPublishes) {
  const payload = node.payload || {};
  if (!Object.prototype.hasOwnProperty.call(payload, 'corr')) {
    fail(`RPC publish ${node.id} missing corr`);
  }
  if (!Object.prototype.hasOwnProperty.call(payload, 'reply_to')) {
    fail(`RPC publish ${node.id} missing reply_to`);
  }
  const replyTo = payload.reply_to;
  const corrRef = payload.corr;
  const hasSubscribe = subscribes.some((sub) => sub.channel === replyTo && sub.filter === corrRef);
  if (!hasSubscribe) {
    fail(`RPC publish ${node.id} lacks matching subscribe for ${replyTo}`);
  }
}
ok('All rpc:req publishes carry corr/reply_to with matching replies.');

const metricPublishes = doc.nodes.filter((n) => n.kind === 'Publish' && typeof n.channel === 'string' && n.channel.startsWith('metric:'));
if (metricPublishes.length === 0) fail('No metric publishes found');
const forbidden = new Set(['name', 'email', 'phone']);
for (const node of metricPublishes) {
  const tags = (node.payload && node.payload.tags) || {};
  for (const key of Object.keys(tags)) {
    if (forbidden.has(key.toLowerCase())) {
      fail(`Metric ${node.id} contains forbidden tag key: ${key}`);
    }
  }
}
ok('Metric publishes avoid PII tag keys.');

console.log('\nAll checks passed.');
