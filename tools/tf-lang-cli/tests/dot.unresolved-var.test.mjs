// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";

import { buildDotGraph } from "../lib/dot.mjs";

test("throws when inputs reference unresolved variables in strict mode", () => {
  const doc = {
    pipeline_id: "demo",
    nodes: [
      { id: "producer", out: "known" },
      { id: "consumer", input: "@ghost" },
    ],
  };

  assert.throws(
    () => buildDotGraph(doc, { strict: true }),
    /Unresolved input variable\(s\): "ghost"/,
  );
});

test("allows unresolved variables when strict mode is disabled", () => {
  const doc = {
    pipeline_id: "demo",
    nodes: [
      { id: "consumer", input: "@ghost" },
    ],
  };

  const dot = buildDotGraph(doc, { strict: false });
  assert.match(dot, /"@ghost" -> "consumer"/);
});

