// @tf-test kind=infra area=tools speed=fast deps=node

import test from "node:test";
import assert from "node:assert/strict";

import { buildDotGraph } from "../lib/dot.mjs";

test("throws when multiple nodes publish the same output variable", () => {
  const doc = {
    pipeline_id: "demo",
    nodes: [
      { id: "first", out: "foo" },
      { id: "second", out: "foo" },
    ],
  };

  assert.throws(
    () => buildDotGraph(doc),
    /Output variable "foo" defined by multiple nodes: "first" and "second"/,
  );
});
