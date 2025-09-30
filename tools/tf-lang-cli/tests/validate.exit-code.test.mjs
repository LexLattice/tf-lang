// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";

test("usage errors take precedence over validation failures", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-validate-exit-"));
  const unknown = join(tmp, "mystery.txt");
  const invalid = join(tmp, "bad.l0.json");

  writeFileSync(unknown, "{}", "utf8");
  writeFileSync(invalid, JSON.stringify({}), "utf8");

  const result = spawnSync("node", ["tools/tf-lang-cli/index.mjs", "validate", unknown, invalid], {
    cwd: process.cwd(),
    encoding: "utf8",
  });

  assert.equal(result.status, 2, `expected exit code 2, got ${result.status}`);
  assert.match(result.stderr, /unable to infer schema/);
  assert.match(result.stderr, /validation failed \[l0\]/);
});
