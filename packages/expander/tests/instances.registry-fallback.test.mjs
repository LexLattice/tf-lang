// @tf-test kind=unit area=expander speed=fast deps=node

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';

const moduleUrl = new URL('../resolve.mjs', import.meta.url).href;
const v2Path = new URL('../../../instances/registry.v2.json', import.meta.url);
const legacyPath = new URL('../../../instances/registry.json', import.meta.url);

test('selectInstance falls back to default when registries fail to load', () => {
  const script = `
 import * as fs from 'node:fs';
import { fileURLToPath } from 'node:url';
const v2 = fileURLToPath(process.argv[2]);
const legacy = fileURLToPath(process.argv[3]);
const v2Backup = fs.readFileSync(v2, 'utf8');
const legacyBackup = fs.readFileSync(legacy, 'utf8');
try {
  fs.writeFileSync(v2, '{ "broken": true', 'utf8');
  fs.writeFileSync(legacy, '{ "broken": true', 'utf8');
const mod = await import(process.argv[1]);
const { selectInstance } = mod;
process.stdout.write(selectInstance({ kind: 'Transform' }) + '\\n');
} finally {
  fs.writeFileSync(v2, v2Backup, 'utf8');
  fs.writeFileSync(legacy, legacyBackup, 'utf8');
}
`;

  const res = spawnSync(
    'node',
    ['--input-type=module', '-e', script, moduleUrl, v2Path.href, legacyPath.href],
    { encoding: 'utf8' }
  );

  assert.equal(res.status, 0, res.stderr);
  assert.equal(res.stdout.trim(), '@Memory');
});
