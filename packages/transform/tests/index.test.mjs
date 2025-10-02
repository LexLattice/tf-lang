// @tf-test kind=product area=transform speed=fast deps=node

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { runTransform } from '../index.mjs';

test('hash blake3 determinism', () => {
  const spec = { op: 'hash', alg: 'blake3' };
  const input = { foo: 'bar', count: 3 };
  const h1 = runTransform(spec, input);
  const h2 = runTransform(spec, input);
  assert.equal(h1, h2);
});

test('digest blake3 and base58 encoding', () => {
  const spec = { op: 'digest', alg: 'blake3' };
  const input = { foo: 'bar' };
  const digest = runTransform(spec, input);
  assert.ok(digest instanceof Uint8Array);
  const encoded = runTransform({ op: 'encode_base58' }, { value: digest });
  assert.equal(encoded, runTransform({ op: 'encode_base58' }, { value: digest }));
});

test('concat maintains deterministic order', () => {
  const value = runTransform({ op: 'concat' }, { b: 'world', a: 'hello ' });
  assert.equal(value, 'hello world');
});

test('concat handles array inputs', () => {
  const value = runTransform({ op: 'concat' }, ['hello', ' ', 'world']);
  assert.equal(value, 'hello world');
});

test('get traverses nested path', () => {
  const result = runTransform({ op: 'get', path: 'user.name' }, { value: { user: { name: 'Ada' } } });
  assert.equal(result, 'Ada');
});

test('get honors legacy spec/input aliases', () => {
  const target = { config: { feature: { flag: true } } };
  assert.equal(runTransform({ op: 'get', key: 'config.feature.flag' }, { value: target }), true);
  assert.equal(runTransform({ op: 'get', path: 'config.feature.flag' }, { source: target }), true);
  assert.equal(runTransform({ op: 'get', path: 'config.feature.flag' }, { obj: target }), true);
  assert.equal(runTransform({ op: 'get', path: 'config.feature.flag' }, { from: target }), true);
});

test('jsonschema.validate uses ajv', () => {
  const schema = {
    type: 'object',
    properties: { id: { type: 'string' } },
    required: ['id'],
    additionalProperties: false,
  };
  const value = { id: 'abc' };
  assert.deepEqual(runTransform({ op: 'jsonschema.validate', schema }, { value }), value);
});

test('model_infer is deterministic', () => {
  const spec = { op: 'model_infer', model: 'demo' };
  const features = { foo: 1, bar: 2 };
  const result1 = runTransform(spec, { features });
  const result2 = runTransform(spec, { features });
  assert.deepEqual(result1, result2);
  assert.ok(['low', 'medium', 'high'].includes(result1.bucket));
});

test('policy_eval deterministic decision', () => {
  const spec = { op: 'policy_eval', policy: 'demo-policy' };
  const input = { severity: 0.3 };
  const r1 = runTransform(spec, { input });
  const r2 = runTransform(spec, { input });
  assert.deepEqual(r1, r2);
  assert.ok(['allow', 'deny'].includes(r1.decision));
});

test('encode_base58 handles strings', () => {
  const encoded = runTransform({ op: 'encode_base58' }, { value: 'hello' });
  assert.equal(encoded, runTransform({ op: 'encode_base58' }, { value: 'hello' }));
});
