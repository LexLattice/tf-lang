import test from 'node:test';
import assert from 'node:assert/strict';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');

test('parser accepts extended literals', () => {
  const src = `write-object(
    key="alpha",
    limit=-1.5,
    enabled=true,
    meta={retry:{count:2}, tags:["a", "b"], flags:[true,false,null]},
    notes=null
  )`;
  const ir = parseDSL(src);
  const args = ir.args;
  assert.equal(args.key, 'alpha');
  assert.equal(args.limit, -1.5);
  assert.equal(args.enabled, true);
  assert.deepEqual(args.meta, {
    retry: { count: 2 },
    tags: ['a', 'b'],
    flags: [true, false, null],
  });
  assert.equal(args.notes, null);
});

test('parser reports location and caret on failure', () => {
  const cases = [
    'write-object(meta={retry:{count:2,})',
    'write-object(name="abc)',
    'write-object(flags=[true false])'
  ];
  for (const src of cases) {
    assert.throws(
      () => parseDSL(src),
      (err) => {
        assert.match(err.message, /\d+:\d+/);
        assert.match(err.message, /\n.*\n.*\^\^/s);
        return true;
      }
    );
  }
});
