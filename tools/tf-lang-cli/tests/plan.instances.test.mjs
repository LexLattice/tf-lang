// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";

test("plan-instances summarizes domains and channel schemes", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-"));
  const file = join(dir, "dag.json");
  const dag = {
    nodes: [
      { id: "pub", kind: "Publish", channel: "rpc:req:claims/submit", qos: "at_least_once" },
      { id: "metric", kind: "Publish", channel: "metric:claims.processed" },
      { id: "transform", kind: "Transform", spec: { op: "noop" } }
    ]
  };
  writeFileSync(file, JSON.stringify(dag, null, 2));

  const res = spawnSync("node", ["tools/tf-lang-cli/index.mjs", "plan-instances", file], {
    encoding: "utf8"
  });

  assert.equal(res.status, 0, res.stderr || res.stdout);
  const summary = JSON.parse(res.stdout);

  assert.equal(summary.domains.interaction.total, 1);
  assert.equal(summary.domains.interaction.instances["@HTTP"], 1);
  assert.equal(summary.domains.obs.total, 1);
  assert.equal(summary.domains.obs.instances["@MetricsMemory"], 1);
  assert.equal(summary.domains.transform.total, 1);
  assert.equal(summary.domains.transform.instances["@Memory"], 1);

  assert.equal(summary.channels["rpc:req"].total, 1);
  assert.equal(summary.channels.metric.total, 1);
  assert.equal(summary.channels.none.total, 1);
  assert.equal(summary.channels["rpc:req"].instances["@HTTP"], 1);
  assert.equal(summary.channels.metric.instances["@MetricsMemory"], 1);
  assert.equal(summary.channels.none.instances["@Memory"], 1);
});
