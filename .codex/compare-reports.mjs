#!/usr/bin/env node
import fs from 'node:fs';
import assert from 'node:assert';

const dir = 'tests/vectors/.out';
const ts = JSON.parse(fs.readFileSync(`${dir}/ts-report.json`, 'utf8'));
const rs = JSON.parse(fs.readFileSync(`${dir}/rs-report.json`, 'utf8'));

const sortByName = arr => arr.sort((a, b) => a.name.localeCompare(b.name));
sortByName(ts);
sortByName(rs);
assert.strictEqual(ts.length, rs.length, 'report length mismatch');
for (let i = 0; i < ts.length; i++) {
  const t = ts[i];
  const r = rs[i];
  assert.strictEqual(t.name, r.name, `name mismatch at index ${i}`);
  assert.deepStrictEqual(t.delta, r.delta, `delta mismatch for ${t.name}`);
  assert.deepStrictEqual(t.effect, r.effect, `effect mismatch for ${t.name}`);
  assert.strictEqual(t.delta_hash, r.delta_hash, `delta hash mismatch for ${t.name}`);
  assert.strictEqual(t.effect_hash, r.effect_hash, `effect hash mismatch for ${t.name}`);
}
console.log('reports match');
