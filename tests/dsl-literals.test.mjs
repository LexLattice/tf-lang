import test from 'node:test';
import assert from 'node:assert/strict';

const parser = await import('../packages/tf-compose/src/parser.mjs');
const formatter = await import('../packages/tf-compose/src/format.mjs');

test('parses extended literals', () => {
  const src = 'write-object(meta={retry:{count:2}, mode:"safe", window:[1,2,], 404:"err"}, tags=[true,false,null,-3.5,], name=foo)';
  const ir = parser.parseDSL(src);
  assert.equal(ir.node, 'Prim');
  assert.equal(ir.prim, 'write-object');
  assert.deepEqual(ir.args.tags, [true, false, null, -3.5]);
  assert.equal(Object.getPrototypeOf(ir.args.meta), null);
  const metaSnapshot = JSON.parse(JSON.stringify(ir.args.meta));
  assert.deepEqual(metaSnapshot, { '404': 'err', mode: 'safe', retry: { count: 2 }, window: [1, 2] });
  assert.equal(ir.args.name, 'foo');
});

test('parses nested structures inside args', () => {
  const src = 'write-object(meta={retry:{count:2, windows:[1,2]}, extra:{enabled:true}})';
  const ir = parser.parseDSL(src);
  const retrySnapshot = JSON.parse(JSON.stringify(ir.args.meta.retry));
  const extraSnapshot = JSON.parse(JSON.stringify(ir.args.meta.extra));
  assert.deepEqual(retrySnapshot, { count: 2, windows: [1, 2] });
  assert.deepEqual(extraSnapshot, { enabled: true });
});

test('object literals keep null prototypes and quote-sensitive keys', () => {
  const src = 'write-object(meta={__proto__:{polluted:true}, constructor:{x:1}, ok:2})';
  const ir = parser.parseDSL(src);
  const meta = ir.args.meta;
  assert.equal(Object.getPrototypeOf(meta), null);
  const snapshot = Object.entries(meta).map(([key, value]) => [key, JSON.parse(JSON.stringify(value))]);
  assert.deepEqual(snapshot, [
    ['__proto__', { polluted: true }],
    ['constructor', { x: 1 }],
    ['ok', 2],
  ]);

  const formatted = formatter.formatDSL(ir);
  const roundTrip = parser.parseDSL(formatted);
  const meta2 = roundTrip.args.meta;
  assert.equal(Object.getPrototypeOf(meta2), null);
  const expected = [
    ['__proto__', { polluted: true }],
    ['constructor', { x: 1 }],
    ['ok', 2],
  ].sort((a, b) => a[0].localeCompare(b[0]));
  const snapshot2 = Object.entries(meta2).map(([key, value]) => [key, JSON.parse(JSON.stringify(value))]);
  assert.deepEqual(snapshot2, expected);
});

test('parse failures include location and caret', () => {
  const cases = [
    'write-object(tags=[1,,2])',
    'write-object(name="unterminated)',
    'write-object(meta={retry:{count:2})',
    'write-object(meta={a:1,,b:2})',
  ];

  for (const src of cases) {
    assert.throws(() => parser.parseDSL(src), (err) => {
      assert.match(err.message, /Parse error at \d+:\d+:/);
      const lines = err.message.split('\n');
      assert.ok(lines.length >= 3, 'error should include snippet');
      const caret = lines[2].trim();
      assert.match(caret, /^\^{2,12}$/);
      return true;
    });
  }
});
