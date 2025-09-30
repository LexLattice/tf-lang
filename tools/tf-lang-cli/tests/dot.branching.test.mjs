#!/usr/bin/env node
import assert from "node:assert/strict";
import { renderPipelineGraph } from "../lib/dot.mjs";

const doc = {
  nodes: [
    {
      id: "T_branch_1",
      kind: "Transform",
      spec: { op: "eq" },
      in: { left: "@input_value", right: "allow" },
      out: { var: "branch_1_value" },
    },
    {
      id: "P_then_path",
      kind: "Publish",
      channel: "metric:then",
      qos: "at_least_once",
      payload: { value: 1 },
      when: "@branch_1_value",
    },
    {
      id: "P_else_path",
      kind: "Publish",
      channel: "metric:else",
      qos: "at_least_once",
      payload: { value: 1 },
      when: { op: "not", var: "branch_1_value" },
    },
  ],
};

const dot = renderPipelineGraph(doc);
const lines = dot.split("\n");

assert(dot.includes("P_then_path") && dot.includes("when: @branch_1_value"), "then branch label should include when guard");
assert(dot.includes("P_else_path") && dot.includes("when: ¬branch_1_value"), "else branch label should include negated guard");

const guardEdges = lines.filter((line) => line.includes("[style=dashed]"));
assert.strictEqual(guardEdges.length, 2, "expected dashed guard edges for both branches");
assert(guardEdges.every((line) => line.includes("n0 ->")), "guard edges should originate from the condition var producer");

const dotNoGuards = renderPipelineGraph(doc, { showWhenEdges: false });
assert(!dotNoGuards.includes("[style=dashed]"), "suppressed guard edges should not render dashed edges");
assert(dotNoGuards.includes("when: @branch_1_value") && dotNoGuards.includes("when: ¬branch_1_value"), "labels should retain when annotations when guard edges hidden");

console.log("dot.branching.test.mjs OK");
