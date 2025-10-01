// @tf-test kind=unit area=expander speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import annotateInstances, { selectInstance, explainInstanceSelection } from '../resolve.mjs';
import expandL2ObjectToL0 from '../expand.mjs';

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

test('annotateInstances preserves instance hints and records resolution', () => {
  const nodes = [
    { kind: 'Publish', channel: 'rpc:req:claims/submit', runtime: { instance: '@Hinted' } }
  ];
  annotateInstances({ nodes });

  assert.equal(nodes[0].runtime.instance, '@HTTP');
  assert.equal(nodes[0].runtime.hint, '@Hinted');
  assert.equal(nodes[0].runtime.resolved, '@HTTP');
});

test('explainInstanceSelection reports rule metadata', () => {
  const node = { kind: 'Publish', channel: 'rpc:req:claims/submit', qos: 'at_least_once' };
  const details = explainInstanceSelection(node);
  assert.equal(details.instance, '@HTTP');
  assert.equal(details.source, 'rule');
  assert.equal(details.ruleIndex, 0);
  assert.ok(details.rule);
});

test('expandL2ObjectToL0 threads instance hints into runtime metadata', () => {
  const doc = {
    pipeline: 'demo.pipeline',
    steps: [
      {
        receive: "interaction.receive(endpoint: 'api/demo', qos: 'at_least_once')"
      }
    ],
    instance_hints: {
      receive: '@Hinted'
    }
  };

  const l0 = expandL2ObjectToL0(doc, { createdAt: '2024-01-01T00:00:00.000Z' });
  const node = l0.nodes.find((entry) => entry.id === 'S_receive');
  assert(node, 'expected receive node');
  assert.equal(node.runtime.hint, '@Hinted');
  assert.equal(node.runtime.instance, '@HTTP');
});
