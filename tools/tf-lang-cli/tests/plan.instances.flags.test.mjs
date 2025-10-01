// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";

function runCli(args, options = {}) {
  const format = options.format ?? "json";
  const formatArgs = format ? ["--format", format] : [];
  return spawnSync("node", ["tools/tf-lang-cli/index.mjs", "plan-instances", ...formatArgs, ...args], {
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

  const res = runCli([`--registry=${registryPath}`, file]);
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

test("plan-instances errors when --registry value is missing", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-missing-reg-"));
  const file = join(dir, "dag.json");
  writeFileSync(file, JSON.stringify({ nodes: [] }, null, 2));

  const res = runCli([file, "--registry"], { format: null });
  assert.equal(res.status, 2);
  assert.match(res.stderr.trim(), /^Error: --registry requires a value\.?$/u);
});

test("plan-instances errors when --group-by value is missing", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-missing-group-"));
  const file = join(dir, "dag.json");
  writeFileSync(file, JSON.stringify({ nodes: [] }, null, 2));

  const res = runCli([file, "--group-by"], { format: null });
  assert.equal(res.status, 2);
  assert.match(res.stderr.trim(), /^Error: --group-by requires a value\.?$/u);
});

test("plan-instances renders table format with grouped totals", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-table-"));
  const file = join(dir, "dag.json");
  const dag = {
    nodes: [
      { id: "rpc", kind: "Publish", channel: "rpc:req:claims/submit" },
      { id: "transform", kind: "Transform", spec: { op: "noop" } }
    ]
  };
  writeFileSync(file, JSON.stringify(dag, null, 2));

  const res = runCli([file], { format: "table" });
  assert.equal(res.status, 0, res.stderr || res.stdout);
  assert.match(res.stdout, /Domain → Instance plan/u);
  assert.match(res.stdout, /interaction\s+TOTAL/u);
  assert.match(res.stdout, /Scheme coverage/u);
});

test("plan-instances --explain adds details section for json", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-explain-json-"));
  const file = join(dir, "dag.json");
  const dag = {
    nodes: [
      { id: "rpc", kind: "Publish", channel: "rpc:req:claims/submit", runtime: { instance: "@Hint" } }
    ]
  };
  writeFileSync(file, JSON.stringify(dag, null, 2));

  const res = runCli(["--explain", file]);
  assert.equal(res.status, 0, res.stderr || res.stdout);
  const payload = JSON.parse(res.stdout);
  assert.ok(Array.isArray(payload.details));
  assert.equal(payload.details[0].hint, "@Hint");
});

test("plan-instances --explain table output highlights hints", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-explain-table-"));
  const file = join(dir, "dag.json");
  const dag = {
    nodes: [
      { id: "rpc", kind: "Publish", channel: "rpc:req:claims/submit", runtime: { instance: "@Hint" } }
    ]
  };
  writeFileSync(file, JSON.stringify(dag, null, 2));

  const res = runCli(["--explain", file], { format: "table" });
  assert.equal(res.status, 0, res.stderr || res.stdout);
  assert.match(res.stdout, /Details:/u);
  assert.match(res.stdout, /hint: @Hint/u);
});

test("plan-instances errors on unknown format", () => {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-plan-instances-bad-format-"));
  const file = join(dir, "dag.json");
  writeFileSync(file, JSON.stringify({ nodes: [] }, null, 2));

  const res = runCli(["--format", "csv", file], { format: null });
  assert.equal(res.status, 2);
  assert.match(res.stderr.trim(), /^--format must be one of: json, table$/u);
});
