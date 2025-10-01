// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";

function runCli(args) {
  return spawnSync("node", ["tools/tf-lang-cli/index.mjs", "plan-instances", ...args], {
    encoding: "utf8"
  });
}

test("plan-instances output is deterministic across runs", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-deterministic-"));
  const file = join(dir, "dag.json");
  const dag = {
    nodes: [
      { id: "a", kind: "Publish", channel: "rpc:req:claims/submit" },
      { id: "b", kind: "Publish", channel: "metric:claims.processed" },
      { id: "c", kind: "Transform", spec: { op: "noop" } }
    ]
  };
  writeFileSync(file, JSON.stringify(dag, null, 2));

  const first = runCli([file]);
  const second = runCli([file]);

  assert.equal(first.status, 0, first.stderr || first.stdout);
  assert.equal(second.status, 0, second.stderr || second.stdout);
  assert.equal(first.stdout, second.stdout);
});
