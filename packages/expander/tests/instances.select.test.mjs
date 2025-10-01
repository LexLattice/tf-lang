// @tf-test kind=unit area=expander speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import annotateInstances, { selectInstance } from '../resolve.mjs';

test('selectInstance uses registry v2 channel rules', () => {
  const node = { kind: 'Publish', channel: 'rpc:req:claims/submit', qos: 'at_least_once' };
  const instance = selectInstance(node);
  assert.equal(instance, '@HTTP');
});

test('selectInstance falls back to default when no rule matches', () => {
  const node = { kind: 'Transform', spec: { op: 'noop' } };
  const instance = selectInstance(node);
  assert.equal(instance, '@Memory');
});

test('annotateInstances annotates runtime domain and instance', () => {
  const nodes = [
    { kind: 'Publish', channel: 'rpc:req:claims/submit', qos: 'at_least_once' },
    { kind: 'Publish', channel: 'metric:claims.processed' },
    { kind: 'Transform', spec: { op: 'noop' } }
  ];
  annotateInstances({ nodes });
  assert.equal(nodes[0].runtime.instance, '@HTTP');
  assert.equal(nodes[0].runtime.domain, 'interaction');
  assert.equal(nodes[1].runtime.instance, '@MetricsMemory');
  assert.equal(nodes[1].runtime.domain, 'obs');
  assert.equal(nodes[2].runtime.instance, '@Memory');
  assert.equal(nodes[2].runtime.domain, 'transform');
});

test('annotateInstances respects explicit domains', () => {
  const explicit = { kind: 'Transform', runtime: { domain: 'custom' } };
  const hinted = { kind: 'Publish', channel: 'metric:claims.processed' };
  annotateInstances({
    nodes: [explicit, hinted],
    domainOf(node) {
      if (node === hinted) return 'observer';
      return undefined;
    }
  });

  assert.equal(explicit.runtime.domain, 'custom');
  assert.equal(hinted.runtime.domain, 'observer');
});
