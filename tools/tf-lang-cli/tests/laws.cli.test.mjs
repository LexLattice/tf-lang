// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync, existsSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";

function writePipeline(tmpDir, fileName, nodes) {
  const pipeline = {
    pipeline_id: "cli.laws.test",
    effects: "Outbound",
    nodes,
  };
  const target = join(tmpDir, fileName);
  writeFileSync(target, JSON.stringify(pipeline, null, 2));
  return target;
}

test("tf laws reports PASS without counterexamples when exclusivity holds", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-laws-pass-"));
  const file = writePipeline(tmp, "pass.l0.json", [
    {
      id: "P_then",
      kind: "Publish",
      channel: "metric:then",
      qos: "at_least_once",
      payload: { value: 1 },
      when: "@decision",
      metadata: { branch: { id: "decision", path: "then" } },
    },
    {
      id: "P_else",
      kind: "Publish",
      channel: "metric:else",
      qos: "at_least_once",
      payload: { value: 1 },
      when: { op: "not", var: "decision" },
      metadata: { branch: { id: "decision", path: "else" } },
    },
    {
      id: "P_record",
      kind: "Publish",
      channel: "policy:record",
      qos: "at_least_once",
      payload: { entry: { id: "1" } },
    },
    {
      id: "P_secure",
      kind: "Publish",
      channel: "policy:secure",
      qos: "at_least_once",
      payload: { envelope: { ciphertext: "ABC" } },
    },
  ]);

  const result = spawnSync("node", ["tools/tf-lang-cli/index.mjs", "laws", "--check", file, "--goal", "branch-exclusive"], {
    cwd: process.cwd(),
    encoding: "utf8",
  });

  assert.equal(result.status, 0, `expected exit 0, got ${result.status}\n${result.stdout}`);
  assert.match(result.stdout, /status: GREEN/);
  assert.match(result.stdout, /branch-exclusive: PASS/);
  assert.match(result.stdout, /monotonic-log: (PASS|WARN)/);
  assert.match(result.stdout, /confidential-envelope: PASS/);
  assert.doesNotMatch(result.stdout, /Counterexample:/);
});

test("tf laws reports RED with counterexample when exclusivity fails", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-laws-fail-"));
  const file = writePipeline(tmp, "fail.l0.json", [
    {
      id: "P_then",
      kind: "Publish",
      channel: "metric:then",
      qos: "at_least_once",
      payload: { value: 1 },
      when: "@decision",
      metadata: { branch: { id: "decision", path: "then" } },
    },
    {
      id: "P_else",
      kind: "Publish",
      channel: "metric:else",
      qos: "at_least_once",
      payload: { value: 1 },
      when: "@decision",
      metadata: { branch: { id: "decision", path: "else" } },
    },
  ]);

  const result = spawnSync("node", [
    "tools/tf-lang-cli/index.mjs",
    "laws",
    "--check",
    file,
    "--goal",
    "branch-exclusive",
    "--max-bools",
    "3",
  ], {
    cwd: process.cwd(),
    encoding: "utf8",
  });

  assert.equal(result.status, 1, `expected exit 1, got ${result.status}\n${result.stdout}`);
  assert.match(result.stdout, /branch-exclusive: RED/);
  assert.match(result.stdout, /Counterexample: .*reason=overlap.*guard=@decision/);
});

test("tf laws --list-goals enumerates known goal identifiers", () => {
  const result = spawnSync("node", ["tools/tf-lang-cli/index.mjs", "laws", "--list-goals"], {
    cwd: process.cwd(),
    encoding: "utf8",
  });

  assert.equal(result.status, 0, `expected exit 0, got ${result.status}\n${result.stdout}`);
  assert.match(result.stdout, /branch-exclusive/);
  assert.match(result.stdout, /monotonic-log/);
  assert.match(result.stdout, /confidential-envelope/);
});

test("tf laws --verbose prints solver evidence path", () => {
  const tmp = mkdtempSync(join(os.tmpdir(), "tf-laws-verbose-"));
  const file = writePipeline(tmp, "verbose.l0.json", [
    {
      id: "P_then",
      kind: "Publish",
      channel: "metric:then",
      qos: "at_least_once",
      payload: { value: 1 },
      when: "@decision",
      metadata: { branch: { id: "decision", path: "then" } },
    },
    {
      id: "P_else",
      kind: "Publish",
      channel: "metric:else",
      qos: "at_least_once",
      payload: { value: 1 },
      when: { op: "not", var: "decision" },
      metadata: { branch: { id: "decision", path: "else" } },
    },
  ]);

  const result = spawnSync(
    "node",
    [
      "tools/tf-lang-cli/index.mjs",
      "laws",
      "--check",
      file,
      "--goal",
      "branch-exclusive",
      "--verbose",
    ],
    { cwd: process.cwd(), encoding: "utf8" },
  );

  assert.equal(result.status, 0, `expected exit 0, got ${result.status}\n${result.stdout}`);
  const match = /evidence: (.*branch-exclusive\.smt2)/.exec(result.stdout);
  assert.ok(match, `expected evidence path in output\n${result.stdout}`);
  const evidencePath = match[1];
  assert.ok(existsSync(evidencePath), `expected evidence file at ${evidencePath}`);
});
