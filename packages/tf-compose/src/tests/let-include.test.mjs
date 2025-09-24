import { test } from 'node:test';
import assert from 'node:assert/strict';

import { parseDSL } from '../parser.mjs';
import { formatDSL } from '../format.mjs';

function stripLoc(value) {
  if (!value || typeof value !== 'object') return value;
  if (Array.isArray(value)) return value.map(stripLoc);
  const next = {};
  for (const [key, val] of Object.entries(value)) {
    if (key === 'loc') continue;
    next[key] = stripLoc(val);
  }
  return next;
}

test('let and include round-trip formatting preserves structure', () => {
  const source = `seq{\n  let account = fetch_account(id="acct-42") |> enrich();\n  process(target=account);\n  include "lib/common.tf";\n}`;
  const parsed = parseDSL(source);
  const formatted = formatDSL(parsed);
  const reparsed = parseDSL(formatted);

  assert.deepStrictEqual(stripLoc(reparsed), stripLoc(parsed));
  assert.match(formatted, /let account =/);
  assert.match(formatted, /include "lib\/common.tf"/);
});

test('let requires an equals token', () => {
  assert.throws(() => {
    parseDSL('seq{ let foo load(); }');
  }, /Expected EQ/);
});

test('let rejects reserved keywords as binding names', () => {
  assert.throws(() => {
    parseDSL('seq{ let seq = fetch(); }');
  }, /Reserved keyword/);
});

test('include requires a string literal path', () => {
  assert.throws(() => {
    parseDSL('seq{ include fetch_config(); }');
  }, /Expected STRING/);
});

test('include may appear at top level', () => {
  const ir = parseDSL('include "lib/common.tf";');
  assert.strictEqual(ir.node, 'Include');
  const formatted = formatDSL(ir);
  assert.strictEqual(formatted.trim(), 'include "lib/common.tf"');
});
