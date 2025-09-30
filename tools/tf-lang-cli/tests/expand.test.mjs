import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import os from "node:os";

import { loadRulebookPlan, rulesForPhase } from "../expand.mjs";

function writeRulebook(yamlSource) {
  const dir = mkdtempSync(join(os.tmpdir(), "tf-expand-"));
  const file = join(dir, "rulebook.yaml");
  writeFileSync(file, yamlSource, "utf8");
  return file;
}

test("expands array phases with inline overrides", () => {
  const rulebookPath = writeRulebook(`
phases:
  - id: base
    rules:
      - shared
      - id: inline-from-map
        expect: override
  - id: child
    inherits:
      - base
    rules:
      - inline-from-map
      - id: inline-custom
        kind: shell
        cmd: echo custom
        expect: ok
      - rule-two
rules:
  shared:
    kind: shell
    cmd: echo shared
    expect: foo
  inline-from-map:
    kind: shell
    cmd: echo map
    expect: default
  rule-two:
    kind: shell
    cmd: echo 2
`);

  const expanded = rulesForPhase(rulebookPath, "child");
  assert.deepStrictEqual(expanded, [
    { id: "shared", kind: "shell", cmd: "echo shared", expect: "foo" },
    { id: "inline-from-map", kind: "shell", cmd: "echo map", expect: "override" },
    { id: "inline-custom", kind: "shell", cmd: "echo custom", expect: "ok" },
    { id: "rule-two", kind: "shell", cmd: "echo 2" },
  ]);
});

test("expands map phases deterministically", () => {
  const rulebookPath = writeRulebook(`
phases:
  base:
    rules:
      - base-rule
  derived:
    inherits:
      - base
    rules:
      - derived-rule
rules:
  base-rule:
    kind: shell
    cmd: echo base
  derived-rule:
    kind: shell
    cmd: echo derived
`);

  const expanded = rulesForPhase(rulebookPath, "derived");
  assert.deepStrictEqual(expanded, [
    { id: "base-rule", kind: "shell", cmd: "echo base" },
    { id: "derived-rule", kind: "shell", cmd: "echo derived" },
  ]);
});

test("dedupes rules by first occurrence across inherits", () => {
  const rulebookPath = writeRulebook(`
phases:
  base:
    rules:
      - shared
      - base-only
  alt:
    rules:
      - shared
      - alt-only
  final:
    inherits:
      - base
      - alt
rules:
  shared:
    kind: shell
    cmd: echo shared
  base-only:
    kind: shell
    cmd: echo base
  alt-only:
    kind: shell
    cmd: echo alt
`);

  const expanded = rulesForPhase(rulebookPath, "final");
  assert.deepStrictEqual(expanded, [
    { id: "shared", kind: "shell", cmd: "echo shared" },
    { id: "base-only", kind: "shell", cmd: "echo base" },
    { id: "alt-only", kind: "shell", cmd: "echo alt" },
  ]);
});

test("errors on unknown phase", () => {
  const rulebookPath = writeRulebook(`
phases:
  known:
    rules: []
`);

  assert.throws(() => rulesForPhase(rulebookPath, "missing"), /unknown phase "missing"/);
});

test("errors on unknown inherited phase", () => {
  const rulebookPath = writeRulebook(`
phases:
  child:
    inherits:
      - ghost
`);

  assert.throws(() => rulesForPhase(rulebookPath, "child"), /invalid inherits reference "ghost"/);
});

test("errors on unknown rule id", () => {
  const rulebookPath = writeRulebook(`
phases:
  only:
    rules:
      - no-rule
`);

  assert.throws(() => rulesForPhase(rulebookPath, "only"), /unknown rule "no-rule"/);
});

test("errors on inline entry missing id", () => {
  const rulebookPath = writeRulebook(`
phases:
  only:
    rules:
      - kind: shell
`);

  assert.throws(
    () => rulesForPhase(rulebookPath, "only"),
    /invalid rule entry at phase "only"/
  );
});

test("errors when phases are not array or object", () => {
  const rulebookPath = writeRulebook(`
phases: 5
`);

  assert.throws(() => rulesForPhase(rulebookPath, "whatever"), /phases must be an array or object/);
});

test("accepts top-level rules array definitions", () => {
  const rulebookPath = writeRulebook(`
phases:
  build:
    rules:
      - lint
rules:
  - id: lint
    kind: shell
    cmd: echo lint
`);

  const expanded = rulesForPhase(rulebookPath, "build");
  assert.deepStrictEqual(expanded, [{ id: "lint", kind: "shell", cmd: "echo lint" }]);
});

test("accepts phase rules map form", () => {
  const rulebookPath = writeRulebook(`
phases:
  build:
    rules:
      lint:
        expect: { code: 0 }
rules:
  lint:
    kind: shell
    cmd: echo lint
`);

  const expanded = rulesForPhase(rulebookPath, "build");
  assert.deepStrictEqual(expanded, [
    { id: "lint", kind: "shell", cmd: "echo lint", expect: { code: 0 } },
  ]);
});

test("errors on invalid rule entry type", () => {
  const rulebookPath = writeRulebook(`
phases:
  build:
    rules:
      - 5
`);

  assert.throws(() => rulesForPhase(rulebookPath, "build"), /invalid rule entry at phase "build"/);
});

test("detects inherits cycles", () => {
  const rulebookPath = writeRulebook(`
phases:
  a:
    inherits: [b]
  b:
    inherits: [a]
`);

  assert.throws(() => rulesForPhase(rulebookPath, "a"), /cycle detected via "a -> b -> a"/);
});

test("normalizeRulebook exposes expanded rules per phase", () => {
  const rulebookPath = writeRulebook(`
phases:
  base:
    rules:
      lint:
        expect: { code: 0 }
  build:
    inherits: [base]
    rules:
      - format
rules:
  lint:
    kind: shell
    cmd: echo lint
  format:
    kind: shell
    cmd: echo format
`);

  const plan = loadRulebookPlan(rulebookPath);
  const build = plan.phases.get("build");
  assert.ok(build);
  assert.deepStrictEqual(
    build.rules,
    [
      { id: "lint", kind: "shell", cmd: "echo lint", expect: { code: 0 } },
      { id: "format", kind: "shell", cmd: "echo format" },
    ],
  );
});
