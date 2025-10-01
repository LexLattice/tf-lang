// @tf-test kind=unit area=expander speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { selectInstance } from '../resolve.mjs';

test('selectInstance matches qos strings and arrays', () => {
  const registry = {
    default: '@Default',
    rules: [
      { when: { qos: 'guaranteed' }, use: '@Guaranteed' },
      { when: { qos: ['best_effort', 'bulk'] }, use: '@Tiered' }
    ]
  };

  assert.equal(selectInstance({ qos: 'guaranteed' }, { registry }), '@Guaranteed');
  assert.equal(
    selectInstance({ qos: { delivery: 'best_effort' } }, { registry }),
    '@Tiered'
  );
});

test('selectInstance matches domain and channel arrays', () => {
  const registry = {
    default: '@Default',
    rules: [
      { when: { domain: ['interaction', 'obs'], channel: ['rpc:req:*', 'metric:*'] }, use: '@Scoped' }
    ]
  };

  const rpcNode = { kind: 'Publish', channel: 'rpc:req:claims/submit' };
  const metricNode = { kind: 'Publish', channel: 'metric:claims.processed' };

  assert.equal(selectInstance(rpcNode, { registry }), '@Scoped');
  assert.equal(selectInstance(metricNode, { registry }), '@Scoped');
});

test('selectInstance respects rule order (first match wins)', () => {
  const registry = {
    default: '@Default',
    rules: [
      { when: { qos: ['gold', 'silver'] }, use: '@Tiered' },
      { when: { qos: 'gold' }, use: '@GoldOnly' }
    ]
  };

  assert.equal(selectInstance({ qos: 'gold' }, { registry }), '@Tiered');
});
