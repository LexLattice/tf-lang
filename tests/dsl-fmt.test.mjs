import test from 'node:test';
import assert from 'node:assert/strict';

const parser = await import('../packages/tf-compose/src/parser.mjs');
const formatter = await import('../packages/tf-compose/src/format.mjs');

test('fmt produces canonical layout', () => {
  const messy = 'seq{ write-object(uri="res://kv/x", key="a", meta={retry:{count:2}, mode:"safe"}, tags=[true,false,null]);write-object(uri="res://kv/x", key="b",); authorize(region="us"){ seq{write-object(key="c", value="3");write-object(key="d", value="4",)} }}';
  const ir = parser.parseDSL(messy);
  const formatted = formatter.formatDSL(ir);
  const expected = [
    'seq{',
    '  write-object(key="a", meta={mode:"safe", retry:{count:2}}, tags=[true, false, null], uri="res://kv/x");',
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
});

test('fmt is idempotent', () => {
  const src = 'write-object(key="x", value="1") |> write-object(key="y", value="2")';
  const ir = parser.parseDSL(src);
  const once = formatter.formatDSL(ir);
  const twice = formatter.formatDSL(parser.parseDSL(once));
  assert.equal(once, twice);
});
