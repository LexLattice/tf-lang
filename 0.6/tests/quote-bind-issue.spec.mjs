#!/usr/bin/env node
import fs from 'node:fs';
import process from 'node:process';
import {
  assertKernelOnly,
  assertRpcPairings,
  assertNoPiiInMetricTags,
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

runCheck('All nodes are kernel primitives.', () => assertKernelOnly(doc));
runCheck('All rpc:req publishes carry corr/reply_to with matching replies.', () => assertRpcPairings(doc));
runCheck('Metric publishes avoid PII tag keys.', () => assertNoPiiInMetricTags(doc));

console.log('\nAll checks passed.');
