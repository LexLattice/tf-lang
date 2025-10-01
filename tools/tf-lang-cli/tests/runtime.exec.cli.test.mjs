// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";

function writePipeline(tmpDir, name, pipeline) {
  const filePath = join(tmpDir, name);
  writeFileSync(filePath, JSON.stringify(pipeline, null, 2), "utf8");
  return filePath;
}

test("runtime exec runs pipelines and prints trace", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-runtime-exec-"));
  const pipeline = {
    pipeline_id: "cli.runtime.exec",
    nodes: [
      {
        id: "T_concat",
        kind: "Transform",
        spec: { op: "concat" },
        in: { parts: ["hello", " ", "world"] },
        out: { var: "message" }
      },
      {
        id: "P_metric",
        kind: "Publish",
        channel: "metric:runtime.exec.test",
        qos: "at_most_once",
        payload: { greeting: "@message" }
      }
    ]
  };
  const file = writePipeline(tmp, "pipeline.l0.json", pipeline);

  const result = spawnSync(
    "node",
    ["tools/tf-lang-cli/index.mjs", "runtime", "exec", file],
    { cwd: process.cwd(), encoding: "utf8" }
  );

  assert.equal(result.status, 0, `expected exit code 0, got ${result.status}`);
  assert(result.stdout.includes("Runtime execution OK"));

  const traced = spawnSync(
    "node",
    ["tools/tf-lang-cli/index.mjs", "runtime", "exec", file, "--trace"],
    { cwd: process.cwd(), encoding: "utf8" }
  );

  assert.equal(traced.status, 0, `expected exit code 0, got ${traced.status}`);
  const traceOut = traced.stdout.trim();
  assert(traceOut.includes("Variables (1)"));
  assert(traceOut.includes("Transforms (1)"));
  assert(traceOut.includes("[deterministic]"));
  assert(traceOut.includes("Publishes (1)"));
});
