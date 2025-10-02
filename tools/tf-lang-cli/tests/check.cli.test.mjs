// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { writeFileSync, mkdirSync } from "node:fs";
import path from "node:path";

const CLI = path.resolve("tools/tf-lang-cli/index.mjs");
const FASTTRACK = path.resolve(
  "examples/v0.6/pipelines/auto.fnol.fasttrack.v1.l0.json"
);

test("tf check --summary reports aggregate statuses", () => {
  const result = spawnSync("node", [CLI, "check", FASTTRACK, "--summary"], {
    encoding: "utf8"
  });

  assert.equal(result.status, 0, result.stderr || result.stdout);
  assert.match(result.stdout, /Overall:\s+GREEN/);
  assert.match(result.stdout, /Effects\s+GREEN/);
  assert.match(result.stdout, /Policy publish\s+GREEN/);
  assert.match(result.stdout, /Laws:/);
  assert.match(result.stdout, /Branch exclusivity/i);
});

test("tf check --json exits nonzero on failures", () => {
  const tmp = path.resolve("out/tmp/check.invalid.json");
  const dir = path.dirname(tmp);
  mkdirSync(dir, { recursive: true });
  const payload = {
    pipeline_id: "invalid",
    effects: "Pure",
    nodes: [
      { id: "pub", kind: "Publish", channel: "rpc:req:test" }
    ]
  };
  writeFileSync(tmp, `${JSON.stringify(payload, null, 2)}\n`, "utf8");

  const check = spawnSync("node", [CLI, "check", tmp, "--json"], {
    encoding: "utf8"
  });

  assert.equal(check.status, 1, check.stdout || check.stderr);
  assert.match(check.stdout, /"status":\s*"RED"/);
});
