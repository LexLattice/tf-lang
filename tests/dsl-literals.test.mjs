import test from 'node:test';
import assert from 'node:assert/strict';

const parser = await import('../packages/tf-compose/src/parser.mjs');

test('parses extended literals', () => {
  const src = 'write-object(meta={retry:{count:2}, mode:"safe"}, tags=[true,false,null,-3.5], name=foo)';
  const ir = parser.parseDSL(src);
  assert.equal(ir.node, 'Prim');
  assert.equal(ir.prim, 'write-object');
  assert.deepEqual(ir.args.tags, [true, false, null, -3.5]);
  assert.deepEqual(ir.args.meta, { mode: 'safe', retry: { count: 2 } });
  assert.equal(ir.args.name, 'foo');
});

test('parses nested structures inside args', () => {
  const src = 'write-object(meta={retry:{count:2, windows:[1,2]}, extra:{enabled:true}})';
  const ir = parser.parseDSL(src);
  assert.deepEqual(ir.args.meta.retry, { count: 2, windows: [1, 2] });
  assert.deepEqual(ir.args.meta.extra, { enabled: true });
});

test('parse failures include location and caret', () => {
  const cases = [
    'write-object(tags=[1,,2])',
    'write-object(name="unterminated)',
    'write-object(meta={retry:{count:2})'
  ];

  for (const src of cases) {
    assert.throws(() => parser.parseDSL(src), (err) => {
      assert.match(err.message, /Parse error at \d+:\d+:/);
      const lines = err.message.split('\n');
      assert.ok(lines.length >= 3, 'error should include snippet');
      assert.match(lines[2], /\^{2,12}/);
      return true;
    });
  }
});
