// @tf-test kind=infra area=runner speed=medium deps=node
import test from 'node:test';
import { readFile } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import assert from 'node:assert/strict';

const LIST_CMD = ['node', ['scripts/test/list.mjs']];
const RUN_CMD = ['node', ['scripts/test/run.mjs', '--kind', 'product', '--speed', 'fast']];

function runCommand([command, args]) {
  const env = { ...process.env };
  delete env.NODE_TEST_CONTEXT;
  const result = spawnSync(command, args, { stdio: 'inherit', env });
  assert.equal(result.status, 0, `${command} ${args.join(' ')} exited with ${result.status}`);
}

test('tests:list and run produce stable outputs', async () => {
  runCommand(LIST_CMD);
  const firstList = await readFile('out/0.4/tests/available.json', 'utf8');

  runCommand(LIST_CMD);
  const secondList = await readFile('out/0.4/tests/available.json', 'utf8');
  assert.equal(firstList, secondList);
  assert.ok(firstList.endsWith('\n'));

  runCommand(RUN_CMD);
  const firstRun = await readFile('out/0.4/tests/manifest.json', 'utf8');

  runCommand(RUN_CMD);
  const secondRun = await readFile('out/0.4/tests/manifest.json', 'utf8');
  assert.equal(firstRun, secondRun);
  assert.ok(firstRun.endsWith('\n'));
});
