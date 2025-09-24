import { test } from 'node:test';
import assert from 'node:assert/strict';

import { parseDSL } from '../parser.mjs';
import { formatDSL } from '../format.mjs';
import { canon } from '../canon.mjs';

test('formatter round-trip preserves let bindings and refs', () => {
  const source = `seq{\n  let account = serialize(payload="hi");\n  account |> hash;\n}`;
  const parsed = parseDSL(source);
  const formatted = formatDSL(parsed);
  const reparsed = parseDSL(formatted);
  assert.deepStrictEqual(stripMeta(reparsed), stripMeta(parsed));
});

test('canon remains stable across format/parse cycles with let nodes', () => {
  const source = `seq{\n  let account = serialize(payload="hi");\n  account |> hash;\n}`;
  const parsed = parseDSL(source);
  const formatted = formatDSL(parsed);
  const reparsed = parseDSL(formatted);

  const canonOriginal = canon(parsed, { laws: [] });
  const canonReparsed = canon(reparsed, { laws: [] });

  assert.deepStrictEqual(stripMeta(canonReparsed), stripMeta(canonOriginal));
});

function stripMeta(value) {
  if (!value || typeof value !== 'object') return value;
  if (Array.isArray(value)) return value.map(stripMeta);
  const result = {};
  for (const [key, val] of Object.entries(value)) {
    if (key === 'loc' || key === 'commutes_with_prev') continue;
    result[key] = stripMeta(val);
  }
  return result;
}
