import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';

import { parseDSL } from '../parser.mjs';
import { expandIncludes } from '../io.mjs';

const samplesDir = resolve(process.cwd(), 'samples/a4');

function collectNodes(node, kind, out = []) {
  if (!node || typeof node !== 'object') return out;
  if (node.node === kind) {
    out.push(node);
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      collectNodes(child, kind, out);
    }
  }
  if (node.node === 'Let') {
    collectNodes(node.init, kind, out);
    collectNodes(node.body, kind, out);
  }
  if (node.node === 'Prim' && node.args) {
    for (const value of Object.values(node.args)) {
      collectNodes(value, kind, out);
    }
  }
  return out;
}

test('expandIncludes replaces include nodes with parsed content', async () => {
  const rootPath = resolve(samplesDir, 'root_with_include.tf');
  const src = await readFile(rootPath, 'utf8');
  const parsed = parseDSL(src);
  const expanded = await expandIncludes(parsed, {
    base: samplesDir,
    stack: [rootPath]
  });

  const includeNodes = collectNodes(expanded, 'Include');
  assert.equal(includeNodes.length, 0, 'expected include nodes to be expanded');

  assert.equal(expanded.node, 'Seq');
  assert.ok(Array.isArray(expanded.children));
  const firstChild = expanded.children[0];
  assert.equal(firstChild.node, 'Seq');
  assert.deepEqual(
    collectNodes(firstChild, 'Prim').map((n) => n.prim),
    ['serialize']
  );
});

test('expandIncludes detects include cycles', async () => {
  const startPath = resolve(samplesDir, 'cycle_a.tf');
  const src = await readFile(startPath, 'utf8');
  const parsed = parseDSL(src);

  await assert.rejects(
    () => expandIncludes(parsed, { base: samplesDir, stack: [startPath] }),
    /IncludeCycle:/
  );
});
