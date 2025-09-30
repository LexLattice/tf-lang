// @tf-test kind=infra area=runner speed=fast deps=node
import test from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import { rm, mkdir, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

import { discoverTests } from '../scripts/test/discover.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, '..');

function toPosix(p) {
  return p.split(path.sep).join('/');
}

test('discoverTests enforces @tf-test headers', async () => {
  const tmpDir = path.join(ROOT, 'tests', '__tmp_harness__');
  await rm(tmpDir, { recursive: true, force: true });
  await mkdir(tmpDir, { recursive: true });

  const withHeaderPath = path.join(tmpDir, 'with-header.test.mjs');
  const missingHeaderPath = path.join(tmpDir, 'missing-header.test.mjs');
  const withHeaderRel = toPosix(path.relative(ROOT, withHeaderPath));
  const missingHeaderRel = toPosix(path.relative(ROOT, missingHeaderPath));

  await writeFile(
    withHeaderPath,
    `// @tf-test kind=infra speed=fast deps=none\n`
      + "import test from 'node:test';\n"
      + "test('fixture with header', () => {});\n",
  );
  await writeFile(
    missingHeaderPath,
    "import test from 'node:test';\n"
      + "test('fixture without header', () => {});\n",
  );

  try {
    await assert.rejects(
      discoverTests(),
      (err) => {
        assert.equal(
          err.message,
          `Missing @tf-test header in ${missingHeaderRel}`,
        );
        return true;
      },
      'discoverTests should require an @tf-test header',
    );

    await rm(missingHeaderPath);

    const tests = await discoverTests();
    const fixture = tests.find((entry) => entry.file === withHeaderRel);
    assert.ok(fixture, 'fixture with header should be discovered');
    assert.equal(fixture.speed, 'fast');
    assert.deepEqual(fixture.deps, []);
  } finally {
    await rm(tmpDir, { recursive: true, force: true });
  }
});
