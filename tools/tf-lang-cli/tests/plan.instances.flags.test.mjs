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

test("plan-instances honors registry override", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-flags-"));
  const file = join(dir, "dag.json");
  const registryPath = join(dir, "registry.json");
  const dag = {
    nodes: [
      { id: "transform", kind: "Transform", spec: { op: "noop" } }
    ]
  };
  writeFileSync(file, JSON.stringify(dag, null, 2));

  const registry = { default: "@Custom", rules: [] };
  writeFileSync(registryPath, JSON.stringify(registry, null, 2));

  const res = runCli(["--registry", registryPath, file]);
  assert.equal(res.status, 0, res.stderr || res.stdout);
  const summary = JSON.parse(res.stdout);
  assert.equal(summary.domains.transform.instances["@Custom"], 1);
  assert.equal(summary.domains.transform.total, 1);
});

test("plan-instances groups by scheme, merges monitors, and sorts keys", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-schemes-"));
  const file = join(dir, "dag.json");
  const dag = {
    nodes: [
      { id: "rpc", kind: "Publish", channel: "rpc:req:claims/submit" },
      { id: "transform", kind: "Transform", spec: { op: "noop" } }
    ],
    monitors: [
      {
        nodes: [
          { id: "metric", kind: "Publish", channel: "metric:claims.processed" },
          { id: "dynamic", kind: "Publish", channel: { var: "monitor_channel" } }
        ]
      }
    ]
  };
  writeFileSync(file, JSON.stringify(dag, null, 2));

  const res = runCli(["--group-by", "scheme", file]);
  assert.equal(res.status, 0, res.stderr || res.stdout);
  const summary = JSON.parse(res.stdout);

  assert.deepEqual(Object.keys(summary.schemes), ["dynamic", "metric", "none", "rpc:req"]);
  assert.equal(summary.schemes["rpc:req"].total, 1);
  assert.equal(summary.schemes.metric.total, 1);
  assert.equal(summary.schemes.dynamic.total, 1);
  assert.equal(summary.schemes.none.total, 1);
  assert.equal(summary.schemes.dynamic.instances["@Memory"], 1);

  assert(summary.domains.interaction.total >= 1);
  assert.equal(summary.domains.transform.total, 1);
});
