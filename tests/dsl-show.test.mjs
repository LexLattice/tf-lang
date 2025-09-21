import test from 'node:test';
import assert from 'node:assert/strict';

const parser = await import('../packages/tf-compose/src/parser.mjs');
const formatter = await import('../packages/tf-compose/src/format.mjs');

test('show renders tree structure', () => {
  const src = 'write-object(uri="res://kv/x", key="a") |> write-object(uri="res://kv/x", key="b")';
  const ir = parser.parseDSL(src);
  const tree = formatter.renderIRTree(ir);
  const lines = tree.split('\n');
  assert.equal(lines[0], 'Seq');
  const primLines = lines.filter((line) => line.trimStart().startsWith('Prim:'));
  assert.equal(primLines.length, 2);
  assert.equal(primLines[0].trim(), 'Prim: write-object {key:"a", uri:"res://kv/x"}');
  assert.equal(primLines[1].trim(), 'Prim: write-object {key:"b", uri:"res://kv/x"}');
});
