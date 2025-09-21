import test from 'node:test';
import assert from 'node:assert/strict';

const parser = await import('../packages/tf-compose/src/parser.mjs');
const formatter = await import('../packages/tf-compose/src/format.mjs');

test('fmt produces canonical layout', () => {
  const messy = 'seq{ write-object(uri="res://kv/x", key="a", meta={"retry mode":"fast","-x":true,plain:1,"404":"err"}, tags=[true,false,null]);write-object(uri="res://kv/x", key="b",); authorize(region="us"){ seq{write-object(key="c", value="3");write-object(key="d", value="4",)} }}';
  const ir = parser.parseDSL(messy);
  const formatted = formatter.formatDSL(ir);
  const expected = [
    'seq{',
    '  write-object(key="a", meta={"-x":true, "404":"err", plain:1, "retry mode":"fast"}, tags=[true, false, null], uri="res://kv/x");',
    '  write-object(key="b", uri="res://kv/x");',
    '  authorize(region="us"){',
      '    seq{',
        '      write-object(key="c", value="3");',
        '      write-object(key="d", value="4")',
      '    }',
      '  }',
      '}'
  ].join('\n');
  assert.equal(formatted, expected);
  assert.match(formatted, /"-x":true/);
  assert.match(formatted, /"404":"err"/);
  assert.match(formatted, /"retry mode":"fast"/);
});

test('fmt is idempotent', () => {
  const src = 'seq{write-object(meta={ "retry mode": "fast", "-x":true, plain:1, }, tags=[true,false,null,], uri="res://kv/x", key="a");write-object(key="b", uri="res://kv/x") }';
  const ir = parser.parseDSL(src);
  const once = formatter.formatDSL(ir);
  const twice = formatter.formatDSL(parser.parseDSL(once));
  assert.equal(once, twice);
  assert.ok(!once.endsWith('\n\n'));
});
