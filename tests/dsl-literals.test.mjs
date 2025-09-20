import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';

test('parses extended literal values', () => {
  const src = 'write-object(num=-3, ratio=2.5, flag=true, other=false, none=null, list=[1, 2, {inner:"y"},], meta={retry:{count:2,},})';
  const ir = parseDSL(src);
  assert.equal(ir.node, 'Prim');
  const args = ir.args;
  assert.equal(args.num, -3);
  assert.equal(args.ratio, 2.5);
  assert.equal(args.flag, true);
  assert.equal(args.other, false);
  assert.equal(args.none, null);
  assert.deepEqual(args.list, [1, 2, { inner: 'y' }]);
  assert.deepEqual(args.meta, { retry: { count: 2 } });
});

test('parse errors include line, column, and caret span', () => {
  const cases = [
    'write-object(list=[1,,2])',
    'write-object(name="abc)',
    'write-object(obj={a:1)'
  ];

  for (const src of cases) {
    try {
      parseDSL(src);
      assert.fail('Expected parse failure for ' + src);
    } catch (err) {
      assert.match(err.message, /\b\d+:\d+\b/, 'includes line:col');
      const lines = err.message.split('\n');
      const pointer = lines[lines.length - 1];
      assert.match(pointer, /\^\^/, 'caret span present');
    }
  }
});
