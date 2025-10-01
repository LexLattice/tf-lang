// Simple test harness for auto.fnol.fasttrack.v1 L0 JSON
// Usage: node tests/fnol-fasttrack.spec.mjs --l0 build/auto.fnol.fasttrack.v1.l0.json

import fs from 'fs';
import process from 'process';

function die(msg) { console.error("FAIL:", msg); process.exit(1); }
function ok(msg)  { console.log("OK  :", msg); }

const argL0 = process.argv.indexOf('--l0');
if (argL0 < 0 || argL0+1 >= process.argv.length) die('Missing --l0 <path>');
const l0Path = process.argv[argL0+1];
const l0 = JSON.parse(fs.readFileSync(l0Path, 'utf-8'));

// 1) Must subscribe to inbound FNOL
const subFnol = l0.nodes.find(n => n.kind === 'Subscribe' && n.channel === 'rpc:req:api/fnol/submit');
if (!subFnol) die('No Subscribe to rpc:req:api/fnol/submit');
ok('Subscribe to FNOL submit present.');

// 2) Must publish payout request with correlation + reply_to
const pubPayout = l0.nodes.find(n => n.kind === 'Publish' && n.channel === 'rpc:req:api/payments/payout');
if (!pubPayout) die('No Publish to rpc:req:api/payments/payout');
if (!pubPayout.payload || !('corr' in pubPayout.payload) || !('reply_to' in pubPayout.payload)) {
  die('Payout publish missing corr/reply_to');
}
ok('Payout publish has corr and reply_to.');

// 3) Metric must not include PII in tags
const metric = l0.nodes.find(n => n.kind === 'Publish' && typeof n.channel === 'string' && n.channel.startsWith('metric:'));
if (!metric) die('No metric publish found');
const tags = (metric.payload && metric.payload.tags) || {};
const banned = ['name','email','phone'];
const hasPII = Object.keys(tags).some(k => banned.includes(k.toLowerCase()));
if (hasPII) die('Metric tags contain PII keys');
ok('Metric tags are clean (no name/email/phone).');

// 4) Effects summary must include both Outbound and Inbound
if (!String(l0.effects).toLowerCase().includes('outbound') || !String(l0.effects).toLowerCase().includes('inbound')) {
  die('Effects do not include both Outbound and Inbound');
}
ok('Effects include Outbound and Inbound.');

// 5) Basic law: request idempotency — for each rpc:req:* publish, ensure corr is present
const rpcPublishes = l0.nodes.filter(n => n.kind === 'Publish' && typeof n.channel === 'string' && n.channel.startsWith('rpc:req:'));
for (const p of rpcPublishes) {
  if (!p.payload || !('corr' in p.payload)) die(`RPC publish ${p.channel} missing corr`);
}
ok('All RPC publishes carry correlation id.');

console.log('\nAll checks passed.');
