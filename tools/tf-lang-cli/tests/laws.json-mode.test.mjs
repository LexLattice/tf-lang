// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";

function writePipeline(tmpDir, fileName, nodes) {
  const pipeline = {
    pipeline_id: "cli.laws.json.test",
    effects: "Outbound",
    nodes,
  };
  const target = join(tmpDir, fileName);
  writeFileSync(target, JSON.stringify(pipeline, null, 2));
  return target;
}

function writeCaps(tmpDir, fileName, data) {
  const target = join(tmpDir, fileName);
  writeFileSync(target, JSON.stringify(data, null, 2));
  return target;
}

const defaultPolicy = join(process.cwd(), "policy", "policy.allow.json");

test("tf laws --json emits deterministic keys and GREEN status", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-laws-json-pass-"));
  const file = writePipeline(tmp, "pass.l0.json", [
    {
      id: "P_then",
      kind: "Publish",
      channel: "metric:then",
      when: "@decision",
      metadata: { branch: { id: "decision", path: "then" } },
    },
    {
      id: "P_else",
      kind: "Publish",
      channel: "metric:else",
      when: { op: "not", var: "decision" },
      metadata: { branch: { id: "decision", path: "else" } },
    },
  ]);
  const capsPath = writeCaps(tmp, "caps.json", []);

  const result = spawnSync(
    "node",
    [
      "tools/tf-lang-cli/index.mjs",
      "laws",
      "--check",
      file,
      "--goal",
      "branch-exclusive",
      "--json",
      "--policy",
      defaultPolicy,
      "--caps",
      capsPath,
    ],
    {
      cwd: process.cwd(),
      encoding: "utf8",
    },
  );

  assert.equal(result.status, 0, `expected exit 0, got ${result.status}\n${result.stdout}`);
  const payload = JSON.parse(result.stdout);
  assert.equal(payload.status, "GREEN");
  assert.deepEqual(Object.keys(payload.laws), [
    "branch_exclusive",
    "monotonic_log",
    "confidential_envelope",
  ]);
  assert.ok(!("counterexample" in payload));
});

test("tf laws --json reports RED status and counterexample payload", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-laws-json-fail-"));
  const file = writePipeline(tmp, "fail.l0.json", [
    {
      id: "P_then",
      kind: "Publish",
      channel: "metric:then",
      when: "@decision",
      metadata: { branch: { id: "decision", path: "then" } },
    },
    {
      id: "P_else",
      kind: "Publish",
      channel: "metric:else",
      when: "@decision",
      metadata: { branch: { id: "decision", path: "else" } },
    },
  ]);
  const capsPath = writeCaps(tmp, "caps.json", []);

  const result = spawnSync(
    "node",
    [
      "tools/tf-lang-cli/index.mjs",
      "laws",
      "--check",
      file,
      "--goal",
      "branch-exclusive",
      "--json",
      "--policy",
      defaultPolicy,
      "--caps",
      capsPath,
    ],
    {
      cwd: process.cwd(),
      encoding: "utf8",
    },
  );

  assert.equal(result.status, 1, `expected exit 1, got ${result.status}\n${result.stdout}`);
  const payload = JSON.parse(result.stdout);
  assert.equal(payload.status, "RED");
  assert.equal(payload.counterexample.goal, "branch-exclusive");
  assert.equal(payload.counterexample.reason, "overlap");
  assert.equal(payload.counterexample.guard, "@decision");
  assert.deepEqual(Object.keys(payload.counterexample.assignment), ["decision"]);
});
