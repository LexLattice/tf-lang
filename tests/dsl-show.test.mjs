import test from 'node:test';
import assert from 'node:assert/strict';

const { parseDSL } = await import('../packages/tf-compose/src/parser.mjs');
const { renderIRTree } = await import('../packages/tf-compose/src/format.mjs');

test('show prints a tree view of the IR', () => {
  const src = 'seq{ write-object(uri="res://kv/x", key="a"); write-object(uri="res://kv/x", key="b") }';
  const ir = parseDSL(src);
  const tree = renderIRTree(ir);
  const lines = tree.split('\n');
  assert.equal(lines[0], 'Seq');
  const firstIdx = lines.findIndex((line) => line.includes('Prim: write-object {key:"a", uri:"res://kv/x"}'));
  const secondIdx = lines.findIndex((line) => line.includes('Prim: write-object {key:"b", uri:"res://kv/x"}'));
  assert.ok(firstIdx >= 0 && secondIdx >= 0);
  assert(firstIdx < secondIdx);
});
