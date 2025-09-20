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
  assert.match(primLines[0], /Prim: write-object .*key:"a"/);
  assert.match(primLines[1], /Prim: write-object .*key:"b"/);
});
