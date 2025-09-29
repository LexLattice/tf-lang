/*
 @tf-test
 kind: product
 speed: fast
 deps: node
*/

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { once } from 'node:events';

const here = dirname(fileURLToPath(import.meta.url));
const scriptPath = resolve(here, '..', '..', '..', 'scripts', 'opt', 'smoke.mjs');

test('tf-opt smoke script succeeds', async () => {
  const proc = spawn(process.execPath, [scriptPath], {
    stdio: 'inherit',
  });
  const [code] = await once(proc, 'exit');
  assert.equal(code, 0);
});
