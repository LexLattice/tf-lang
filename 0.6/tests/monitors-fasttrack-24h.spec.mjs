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

const monitors = doc.monitors ?? [];
const allNodes = monitors.flatMap((m) => m.nodes ?? []);

if (allNodes.length === 0) fail('No monitor nodes found');

const rpcPublishes = allNodes.filter((node) => node.kind === 'Publish' && typeof node.channel === 'string' && node.channel.startsWith('rpc:req:'));
const subscribes = allNodes.filter((node) => node.kind === 'Subscribe');

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
if (rpcPublishes.length > 0) ok('All rpc:req publishes carry corr/reply_to with matching replies.');

const metricPublishes = allNodes.filter((node) => node.kind === 'Publish' && typeof node.channel === 'string' && node.channel.startsWith('metric:'));
const forbidden = new Set(['name', 'email', 'phone']);
for (const node of metricPublishes) {
  const tags = (node.payload && node.payload.tags) || {};
  for (const key of Object.keys(tags)) {
    if (forbidden.has(key.toLowerCase())) {
      fail(`Metric ${node.id} contains forbidden tag key: ${key}`);
    }
  }
}
if (metricPublishes.length > 0) ok('Metric publishes avoid PII tag keys.');

const effectSet = new Set((doc.effects || '').split('+').filter(Boolean));
if (!effectSet.has('Outbound')) {
  fail('Effects summary missing Outbound');
}
const hasReplySubscribe = subscribes.some((node) => typeof node.channel === 'string' && node.channel.startsWith('@reply_to_'));
if (hasReplySubscribe && !effectSet.has('Inbound')) {
  fail('Effects summary missing Inbound for reply subscriptions');
}
ok('Effects summary includes required capabilities.');

console.log('\nAll checks passed.');
