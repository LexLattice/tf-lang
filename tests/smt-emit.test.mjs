// @tf-test kind=proofs area=smt speed=medium deps=node
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

import { parseDSL } from '../packages/tf-compose/src/parser.mjs';
import { emitSMT } from '../packages/tf-l0-proofs/src/smt.mjs';

const conflictFlow = new URL('../examples/flows/storage_conflict.tf', import.meta.url);
const okFlow = new URL('../examples/flows/storage_ok.tf', import.meta.url);
const catalogUrl = new URL('../packages/tf-l0-spec/spec/catalog.json', import.meta.url);

const catalogPromise = readFile(catalogUrl, 'utf8').then((raw) => JSON.parse(raw));

async function loadIR(url) {
  const source = await readFile(url, 'utf8');
  const ir = parseDSL(source);
  const catalog = await catalogPromise;
  annotateWrites(ir, catalog);
  return ir;
}

test('storage_conflict emits conflict assertions', async () => {
  const ir = await loadIR(conflictFlow);
  const smt = emitSMT(ir);
  assert.ok(/\(assert \(not \(or /.test(smt), 'should include global validity assert');
  const declared = smt.match(/\(declare-const\s+conflict_/g) || [];
  assert.ok(declared.length >= 1, 'at least one conflict declared');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

test('storage_ok emits deterministic model without conflicts', async () => {
  const ir = await loadIR(okFlow);
  const first = emitSMT(ir);
  const second = emitSMT(ir);
  assert.equal(first, second, 'emission is deterministic');
  const declared = first.match(/\(declare-const\s+conflict_/g) || [];
  assert.equal(declared.length, 0, 'no conflicts declared for sequential flow');
  assert.ok(first.includes('(assert true)'), 'validity assert handles no conflicts');
  assert.ok(/\(check-sat\)\s*$/.test(first), 'ends with check-sat');
});

test('multi-write branch conflicts on shared target', async () => {
  const catalog = await catalogPromise;
  const ir = parseDSL(`authorize{
    par{
      seq{
        write-object(uri="res://a", key="x", value="1");
        write-object(uri="res://b", key="x", value="2")
      };
      write-object(uri="res://b", key="y", value="3")
    }
  }`);
  annotateWrites(ir, catalog);
  const smt = emitSMT(ir);
  const declared = smt.match(/\(declare-const\s+conflict_/g) || [];
  assert.ok(declared.length >= 1, 'at least one conflict declared');
  assert.ok(smt.includes('(= "res://b" "res://b")'), 'conflict pairs include res://b vs res://b');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

test('read-only par produces no conflicts', async () => {
  const catalog = await catalogPromise;
  const ir = parseDSL(`authorize{
    par{
      read-object(uri="res://a", key="1");
      read-object(uri="res://b", key="2")
    }
  }`);
  annotateWrites(ir, catalog);
  const smt = emitSMT(ir);
  assert.ok(!/\(declare-const\s+conflict_/.test(smt), 'no conflict vars declared');
  assert.ok(smt.includes('(assert true)'), 'falls back to assert true');
  assert.ok(/\(check-sat\)\s*$/.test(smt), 'ends with check-sat');
});

function annotateWrites(ir, catalog) {
  const index = buildCatalogIndex(catalog);
  walk(ir, (node) => {
    if (!node || typeof node !== 'object') {
      return;
    }
    if (node.node === 'Prim') {
      const primName = typeof node.prim === 'string' ? node.prim.toLowerCase() : '';
      const prim = index.get(primName);
      if (!prim) {
        return;
      }
      const writes = concretizeWrites(prim.writes, node.args);
      if (writes.length > 0) {
        node.writes = writes;
      }
    }
  });
}

function buildCatalogIndex(catalog = {}) {
  const index = new Map();
  for (const prim of catalog.primitives || []) {
    if (prim && typeof prim.name === 'string') {
      index.set(prim.name.toLowerCase(), prim);
    }
  }
  return index;
}

function concretizeWrites(writes = [], args = {}) {
  if (!Array.isArray(writes) || writes.length === 0) {
    return [];
  }
  const seen = new Set();
  const result = [];
  for (const entry of writes) {
    const uri = concretizeUri(entry?.uri, args);
    if (!uri || seen.has(uri)) {
      continue;
    }
    seen.add(uri);
    result.push({ ...entry, uri });
  }
  result.sort((a, b) => a.uri.localeCompare(b.uri));
  return result;
}

function concretizeUri(uri, args = {}) {
  if (isConcreteUri(uri)) {
    return uri;
  }
  const fromArgs = selectUriFromArgs(args);
  return isConcreteUri(fromArgs) ? fromArgs : null;
}

function isConcreteUri(uri) {
  return typeof uri === 'string' && uri.length > 0 && uri !== 'res://unknown' && !/[<>]/.test(uri);
}

function selectUriFromArgs(args = {}) {
  if (!args || typeof args !== 'object') {
    return null;
  }
  const keys = ['uri', 'resource_uri', 'bucket_uri'];
  for (const key of keys) {
    const value = args[key];
    if (typeof value === 'string' && value.length > 0) {
      return value;
    }
  }
  return null;
}

function walk(node, visit) {
  if (!node || typeof node !== 'object') {
    return;
  }
  visit(node);
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      walk(child, visit);
    }
  }
}
