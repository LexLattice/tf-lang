#!/usr/bin/env node
import fs from 'node:fs';
import process from 'node:process';
import {
  assertKernelOnly,
  assertRpcPairings,
  assertNoPiiInMetricTags,
  extractNodes,
} from './_util/l0-checks.mjs';

function fail(msg) {
  console.error('FAIL:', msg);
  process.exit(1);
}

function ok(msg) {
  console.log('OK  :', msg);
}

function runCheck(label, fn) {
  try {
    fn();
    ok(label);
  } catch (err) {
    fail(err?.message ?? String(err));
  }
}

const argIndex = process.argv.indexOf('--l0');
if (argIndex < 0 || argIndex + 1 >= process.argv.length) fail('Missing --l0 <path>');
const l0Path = process.argv[argIndex + 1];
const doc = JSON.parse(fs.readFileSync(l0Path, 'utf8'));

const nodes = extractNodes(doc);
if (nodes.length === 0) fail('No monitor nodes found');

runCheck('Monitor bundle is kernel-only.', () => assertKernelOnly(doc));
runCheck('All rpc:req publishes carry corr/reply_to with matching replies.', () => assertRpcPairings(doc));
runCheck('Metric publishes avoid PII tag keys.', () => assertNoPiiInMetricTags(doc));

const effectSet = new Set((doc.effects || '').split('+').filter(Boolean));
if (!effectSet.has('Outbound')) {
  fail('Effects summary missing Outbound');
}
const hasReplySubscribe = nodes.some((node) => node.kind === 'Subscribe' && typeof node.channel === 'string' && node.channel.startsWith('@reply_to_'));
if (hasReplySubscribe && !effectSet.has('Inbound')) {
  fail('Effects summary missing Inbound for reply subscriptions');
}
ok('Effects summary includes required capabilities.');

console.log('\nAll checks passed.');
