import test from 'node:test';
import assert from 'node:assert/strict';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { formatDSL } = await import('../packages/tf-compose/src/format.mjs');

test('fmt normalizes spacing and ordering deterministically', () => {
  const messy = 'seq{ write-object(uri="res://kv/x", key="b", meta={ retry:{ count:2,}, enabled:true }, flags=[true,false,], limit=-1.5);read-object(key="a", uri="res://kv/x", tags=["z","a"], meta={enabled:false}) }';
  const ir = parseDSL(messy);
  const formatted = formatDSL(ir);
  const expected = [
    'seq{',
    '  write-object(flags=[true, false], key="b", limit=-1.5, meta={enabled:true, retry:{count:2}}, uri="res://kv/x");',
    '  read-object(key="a", meta={enabled:false}, tags=["z", "a"], uri="res://kv/x")',
    '}'
  ].join('\n');
  assert.equal(formatted, expected);
  const reformatted = formatDSL(parseDSL(formatted));
  assert.equal(reformatted, formatted);
});
