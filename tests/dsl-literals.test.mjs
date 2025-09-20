import test from 'node:test';
import assert from 'node:assert/strict';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');

test('parses numbers, booleans, null, arrays, and objects', () => {
  const src = `seq{
    write-object(
      arr=[1, 2.5, -0.25, true, false, null, {inner:true}],
      flag=true,
      meta={retry:{count:2}, "retry-mode": "fast"},
      name="alpha",
      nested={child:{count:2}},
      note=fast,
      value=-42
    )
  }`;
  const ir = parseDSL(src);
  assert.equal(ir.node, 'Seq');
  assert.equal(ir.children.length, 1);
  const prim = ir.children[0];
  assert.equal(prim.node, 'Prim');
  assert.equal(prim.args.flag, true);
  assert.equal(prim.args.value, -42);
  assert.deepEqual(prim.args.arr, [1, 2.5, -0.25, true, false, null, { inner: true }]);
  assert.deepEqual(prim.args.meta, { retry: { count: 2 }, 'retry-mode': 'fast' });
  assert.deepEqual(prim.args.nested, { child: { count: 2 } });
  assert.equal(prim.args.note, 'fast');
  assert.equal(prim.args.name, 'alpha');
});

const failureCases = [
  {
    name: 'extra comma in array',
    src: 'seq{ write-object(arr=[1,,2]) }',
  },
  {
    name: 'unterminated string',
    src: 'seq{ write-object(name="alpha) }',
  },
  {
    name: 'unclosed object',
    src: 'seq{ write-object(meta={retry:{count:2}) }',
  },
];

for (const { name, src } of failureCases) {
  test(`parse failure emits location for ${name}`, () => {
    assert.throws(() => parseDSL(src), (err) => {
      assert.match(err.message, /at \d+:\d+/);
      assert.match(err.message, /\n.*\n\s*\^{2,}/);
      return true;
    });
  });
}
